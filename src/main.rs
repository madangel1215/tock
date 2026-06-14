// Tock - Terminal calendar TUI
// Feature and visual clone of Timely (Ruby), built on Crust.


mod config;
mod database;
mod ics;
mod notifications;
mod poller;
mod sources;
mod weather;

use crust::{display_width, strip_ansi, Crust, Cursor, Input, Pane, style};
use database::{Database, Event, EventData};
use std::collections::HashMap;
use std::sync::{mpsc, Arc};
use std::path::Path;

// =========================================================================
// Date arithmetic helpers
// =========================================================================

fn days_in_month(year: i32, month: u32) -> u32 {
    orbit::days_in_month(year, month)
}

fn is_leap(year: i32) -> bool {
    (year % 4 == 0 && year % 100 != 0) || year % 400 == 0
}

/// ISO weekday: Monday=1, Sunday=7
fn cwday(year: i32, month: u32, day: u32) -> u32 {
    // Tomohiko Sakamoto's algorithm
    let t = [0i32, 3, 2, 5, 0, 3, 5, 1, 4, 6, 2, 4];
    let y = if month < 3 { year - 1 } else { year };
    let d = ((y + y / 4 - y / 100 + y / 400 + t[(month - 1) as usize] + day as i32)
        % 7) as u32;
    if d == 0 { 7 } else { d }
}

/// ISO week number
fn cweek(year: i32, month: u32, day: u32) -> u32 {
    let doy = day_of_year(year, month, day) as i32;
    let dow = cwday(year, month, day) as i32;
    let _jan1_dow = cwday(year, 1, 1) as i32;
    let mut wk = (doy - dow + 10) / 7;
    if wk < 1 {
        // Belongs to last week of previous year
        let prev_jan1 = cwday(year - 1, 1, 1) as i32;
        let prev_dec31 = if is_leap(year - 1) { 366 } else { 365 };
        wk = (prev_dec31 - cwday(year - 1, 12, 31) as i32 + 10) / 7;
        let _ = prev_jan1; // silence warning
    } else if wk > 52 {
        let dec31_dow = cwday(year, 12, 31) as i32;
        if dec31_dow < 4 {
            wk = 1;
        }
    }
    wk.max(1) as u32
}

fn day_of_year(year: i32, month: u32, day: u32) -> u32 {
    let mut doy = 0;
    for m in 1..month {
        doy += days_in_month(year, m);
    }
    doy + day
}

fn add_months(date: (i32, u32, u32), n: i32) -> (i32, u32, u32) {
    let (y, m, d) = date;
    let total = (y * 12 + m as i32 - 1) + n;
    let ny = total.div_euclid(12);
    let nm = (total.rem_euclid(12) + 1) as u32;
    let max_d = days_in_month(ny, nm);
    (ny, nm, d.min(max_d))
}

fn date_to_ts(year: i32, month: u32, day: u32, hour: u32, min: u32, sec: u32) -> i64 {
    // Hinnant's algorithm for days from civil
    let y = if month <= 2 { year - 1 } else { year } as i64;
    let m = if month <= 2 { month + 9 } else { month - 3 } as i64;
    let d = day as i64;
    let era = if y >= 0 { y } else { y - 399 } / 400;
    let yoe = y - era * 400;
    let doy = (153 * m + 2) / 5 + d - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    let days = era * 146097 + doe - 719468;
    days * 86400 + hour as i64 * 3600 + min as i64 * 60 + sec as i64
}

fn ts_to_parts(ts: i64) -> (i32, u32, u32, u32, u32, u32) {
    let secs = ts.rem_euclid(86400);
    let days = ts.div_euclid(86400);
    let z = days + 719468;
    let era = if z >= 0 { z } else { z - 146096 } / 146097;
    let doe = z - era * 146097;
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = if m <= 2 { y + 1 } else { y };
    (
        y as i32,
        m as u32,
        d as u32,
        (secs / 3600) as u32,
        ((secs % 3600) / 60) as u32,
        (secs % 60) as u32,
    )
}

fn today() -> (i32, u32, u32) {
    let now = database::now_secs();
    // Apply local timezone offset
    let tz_offset = local_tz_offset_secs();
    let local = now + tz_offset;
    let (y, m, d, _, _, _) = ts_to_parts(local);
    (y, m, d)
}

/// One quote from the quotes file: English text (may end with "— author"),
/// plus an optional Chinese explanation after a fullwidth ｜ separator.
struct Quote {
    en: String,
    zh: Option<String>,
}

/// Load quotes from a markdown file: every `- ` bullet line is one quote,
/// `english — author ｜ 中文解釋` (｜ part optional).
fn load_quotes(path: &str) -> Vec<Quote> {
    std::fs::read_to_string(path)
        .map(|s| {
            // Skip YAML frontmatter, else `tags:\n  - personal` becomes a
            // "quote" on the wall.
            let body = match s.strip_prefix("---") {
                Some(rest) => match rest.find("\n---") {
                    Some(i) => &rest[i + 4..],
                    None => s.as_str(),
                },
                None => s.as_str(),
            };
            // The note is "docs above, quotes below" — only bullets after the
            // LAST `---` separator count, so explanatory `- ` lines in the
            // header don't leak onto the wall. No separator → take them all.
            let body = match body.lines().enumerate().filter(|(_, l)| l.trim() == "---").last() {
                Some((idx, _)) => {
                    let skip: usize = body.lines().take(idx + 1).map(|l| l.len() + 1).sum();
                    &body[skip.min(body.len())..]
                }
                None => body,
            };
            body.lines()
                .filter_map(|l| l.trim().strip_prefix("- "))
                .filter_map(|q| {
                    let (en, zh) = match q.split_once('｜') {
                        Some((e, z)) => {
                            let z = z.trim();
                            (e.trim(), if z.is_empty() { None } else { Some(z.to_string()) })
                        }
                        None => (q.trim(), None),
                    };
                    // English-practice pool: skip bullets with no English
                    // letters (純中文句 belongs in the note header, not here).
                    if en.is_empty() || !en.chars().any(|c| c.is_ascii_alphabetic()) {
                        None
                    } else {
                        Some(Quote { en: en.to_string(), zh })
                    }
                })
                .collect()
        })
        .unwrap_or_default()
}

/// Split "quote — author" on the LAST " — " (spaced em dash).
fn split_author(en: &str) -> (&str, Option<&str>) {
    match en.rfind(" — ") {
        Some(i) => (en[..i].trim_end(), Some(en[i + " — ".len()..].trim())),
        None => (en, None),
    }
}

/// Which quote is "current": deterministic hash of the hour bucket, so the
/// wall and the practice popup agree and redraws within an hour are stable.
fn quote_index(len: usize) -> usize {
    let bucket = (database::now_secs() + local_tz_offset_secs()) / 3600;
    ((bucket as u64).wrapping_mul(2654435761) % len as u64) as usize
}

fn practice_log_path() -> std::path::PathBuf {
    config::tock_home().join("quote_practice.log")
}

/// How many times this quote was typed perfectly (errors == 0).
fn practice_success_count(en: &str) -> usize {
    std::fs::read_to_string(practice_log_path())
        .map(|s| {
            s.lines()
                .filter(|l| {
                    let mut f = l.splitn(4, '\t');
                    let _ts = f.next();
                    let ok = f.next() == Some("1");
                    let _errs = f.next();
                    ok && f.next() == Some(en)
                })
                .count()
        })
        .unwrap_or(0)
}

fn append_practice_log(en: &str, errors: usize) {
    use std::io::Write;
    if let Ok(mut f) = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(practice_log_path())
    {
        let ok = if errors == 0 { 1 } else { 0 };
        let _ = writeln!(f, "{}\t{}\t{}\t{}", database::now_secs(), ok, errors, en);
    }
}

/// Char-level LCS diff. Returns (target_hit, typed_ok): false = a target char
/// the user missed / a typed char that is wrong or extra.
fn char_diff(target: &[char], typed: &[char]) -> (Vec<bool>, Vec<bool>) {
    let n = target.len();
    let m = typed.len();
    let mut dp = vec![vec![0u32; m + 1]; n + 1];
    for i in (0..n).rev() {
        for j in (0..m).rev() {
            dp[i][j] = if target[i] == typed[j] {
                dp[i + 1][j + 1] + 1
            } else {
                dp[i + 1][j].max(dp[i][j + 1])
            };
        }
    }
    let mut hit = vec![false; n];
    let mut ok = vec![false; m];
    let (mut i, mut j) = (0, 0);
    while i < n && j < m {
        if target[i] == typed[j] {
            hit[i] = true;
            ok[j] = true;
            i += 1;
            j += 1;
        } else if dp[i + 1][j] >= dp[i][j + 1] {
            i += 1;
        } else {
            j += 1;
        }
    }
    (hit, ok)
}

/// Greedy display-width wrap, CJK-safe: breaks at spaces when possible,
/// hard-breaks long unspaced runs (Chinese) per character.
fn wrap_display(text: &str, width: usize) -> Vec<String> {
    let width = width.max(4);
    let mut lines: Vec<String> = Vec::new();
    let mut cur = String::new();
    let mut cur_w = 0usize;
    for word in text.split_whitespace() {
        let ww = display_width(word);
        if ww <= width {
            let sep = if cur.is_empty() { 0 } else { 1 };
            if cur_w + sep + ww > width {
                lines.push(std::mem::take(&mut cur));
                cur_w = 0;
            }
            if !cur.is_empty() {
                cur.push(' ');
                cur_w += 1;
            }
            cur.push_str(word);
            cur_w += ww;
        } else {
            for ch in word.chars() {
                let cw = display_width(&ch.to_string());
                if cur_w + cw > width {
                    lines.push(std::mem::take(&mut cur));
                    cur_w = 0;
                }
                cur.push(ch);
                cur_w += cw;
            }
        }
    }
    if !cur.is_empty() {
        lines.push(cur);
    }
    lines
}

fn now_slot() -> i32 {
    let now = database::now_secs();
    let tz_offset = local_tz_offset_secs();
    let local = now + tz_offset;
    let (_, _, _, h, m, _) = ts_to_parts(local);
    (h * 2 + if m >= 30 { 1 } else { 0 }) as i32
}

/// Get local timezone offset in seconds from UTC via libc
fn local_tz_offset_secs() -> i64 {
    unsafe {
        let now = database::now_secs() as libc::time_t;
        let mut tm: libc::tm = std::mem::zeroed();
        libc::localtime_r(&now, &mut tm);
        tm.tm_gmtoff as i64
    }
}

/// Format a weekday name from ISO weekday number
fn weekday_short(wd: u32) -> &'static str {
    match wd {
        1 => "Mon", 2 => "Tue", 3 => "Wed", 4 => "Thu",
        5 => "Fri", 6 => "Sat", 7 => "Sun", _ => "???",
    }
}

fn weekday_long(wd: u32) -> &'static str {
    match wd {
        1 => "Monday", 2 => "Tuesday", 3 => "Wednesday", 4 => "Thursday",
        5 => "Friday", 6 => "Saturday", 7 => "Sunday", _ => "Unknown",
    }
}

fn month_name(m: u32) -> &'static str {
    match m {
        1 => "January", 2 => "February", 3 => "March", 4 => "April",
        5 => "May", 6 => "June", 7 => "July", 8 => "August",
        9 => "September", 10 => "October", 11 => "November", 12 => "December",
        _ => "?",
    }
}

fn month_short(m: u32) -> &'static str {
    match m {
        1 => "Jan", 2 => "Feb", 3 => "Mar", 4 => "Apr",
        5 => "May", 6 => "Jun", 7 => "Jul", 8 => "Aug",
        9 => "Sep", 10 => "Oct", 11 => "Nov", 12 => "Dec",
        _ => "?",
    }
}

fn format_date_long(y: i32, m: u32, d: u32) -> String {
    let wd = cwday(y, m, d);
    format!("{}, {} {:02}, {}", weekday_long(wd), month_name(m), d, y)
}

fn format_date_short(y: i32, m: u32, d: u32) -> String {
    let wd = cwday(y, m, d);
    format!("{} {} {:02}, {}", weekday_short(wd), month_short(m), d, y)
}

// =========================================================================
// App
// =========================================================================

struct App {
    db: Arc<Database>,
    config: config::Config,
    running: bool,
    selected_date: (i32, u32, u32),
    selected_slot: i32,
    slot_offset: i32,
    selected_event_index: usize,
    events_by_date: HashMap<(i32, u32, u32), Vec<Event>>,
    weather_forecast: HashMap<String, weather::DayForecast>,
    weather_fetched_at: i64,

    info: Pane,
    top: Pane,
    mid: Pane,
    bottom: Pane,
    status: Pane,

    rows: u16,
    cols: u16,

    cached_planets_date: Option<(i32, u32, u32)>,
    cached_planets: Vec<String>,
    allday_count_date: Option<(i32, u32, u32)>,
    allday_count: usize,

    syncing: bool,
    // True while the practice popup is open — hides the wall quote so the
    // answer isn't visible behind the recall exercise.
    hide_wall_quote: bool,
    poller_rx: mpsc::Receiver<poller::PollerEvent>,
    _poller_tx: mpsc::Sender<poller::PollerEvent>,
}

impl App {
    fn new() -> Self {
        let db = Arc::new(Database::new(None).expect("Failed to open database"));
        let cfg = config::Config::new();
        let (cols, rows) = Crust::terminal_size();

        let top_h: u16 = 10;
        let bottom_h = ((rows as f64 * 0.2) as u16).max(5);
        let mid_h = rows.saturating_sub(2 + top_h + bottom_h).max(4);
        let bottom_h = if 2 + top_h + mid_h + bottom_h > rows {
            rows.saturating_sub(2 + top_h + mid_h).max(3)
        } else {
            bottom_h
        };

        let info_bg = cfg.get_i64("colors.info_bg", 235) as u16;
        let status_bg = cfg.get_i64("colors.status_bg", 235) as u16;

        let mut info = Pane::new(1, 1, cols, 1, 255, info_bg);
        info.border = false;
        info.scroll = false;

        let mut top = Pane::new(1, 2, cols, top_h, 255, 0);
        top.border = false;
        top.scroll = false;

        let mut mid = Pane::new(1, 2 + top_h, cols, mid_h, 255, 0);
        mid.border = false;
        mid.scroll = false;

        let mut bottom = Pane::new(1, 2 + top_h + mid_h, cols, bottom_h, 255, 0);
        bottom.border = false;
        bottom.scroll = false;

        let mut status = Pane::new(1, rows, cols, 1, 252, status_bg);
        status.border = false;
        status.scroll = false;

        let (tx, rx) = mpsc::channel();

        let slot = now_slot();

        App {
            db,
            config: cfg,
            running: true,
            selected_date: today(),
            selected_slot: slot,
            slot_offset: (slot - 5).max(0),
            selected_event_index: 0,
            events_by_date: HashMap::new(),
            weather_forecast: HashMap::new(),
            weather_fetched_at: 0,
            info,
            top,
            mid,
            bottom,
            status,
            rows,
            cols,
            cached_planets_date: None,
            cached_planets: Vec::new(),
            allday_count_date: None,
            allday_count: 0,
            syncing: false,
            hide_wall_quote: false,
            poller_rx: rx,
            _poller_tx: tx,
        }
    }

    // =====================================================================
    // Pane recreation
    // =====================================================================

    fn recreate_panes(&mut self) {
        let (cols, rows) = Crust::terminal_size();
        self.cols = cols;
        self.rows = rows;

        let top_h: u16 = 10;
        let mut bottom_h = ((rows as f64 * 0.2) as u16).max(5);
        let mid_h = rows.saturating_sub(2 + top_h + bottom_h).max(4);
        if 2 + top_h + mid_h + bottom_h > rows {
            bottom_h = rows.saturating_sub(2 + top_h + mid_h).max(3);
        }

        let info_bg = self.config.get_i64("colors.info_bg", 235) as u16;
        let status_bg = self.config.get_i64("colors.status_bg", 235) as u16;

        self.info = Pane::new(1, 1, cols, 1, 255, info_bg);
        self.info.border = false;
        self.info.scroll = false;

        self.top = Pane::new(1, 2, cols, top_h, 255, 0);
        self.top.border = false;
        self.top.scroll = false;

        self.mid = Pane::new(1, 2 + top_h, cols, mid_h, 255, 0);
        self.mid.border = false;
        self.mid.scroll = false;

        self.bottom = Pane::new(1, 2 + top_h + mid_h, cols, bottom_h, 255, 0);
        self.bottom.border = false;
        self.bottom.scroll = false;

        self.status = Pane::new(1, rows, cols, 1, 252, status_bg);
        self.status.border = false;
        self.status.scroll = false;
    }

    // =====================================================================
    // All-day count (max across visible week, cached per date)
    // =====================================================================

    fn allday_count(&mut self) -> usize {
        if self.allday_count_date == Some(self.selected_date) {
            return self.allday_count;
        }
        let (sy, sm, sd) = self.selected_date;
        let wd = cwday(sy, sm, sd);
        let tz = local_tz_offset_secs();
        let mut max = 0usize;
        for i in 0..7 {
            let offset = i as i32 - (wd as i32 - 1);
            let d = add_days(self.selected_date, offset);
            let n = self.events_by_date.get(&d)
                .map(|evts| evts.iter().filter(|e| e.all_day || is_background_span(e, tz)).count())
                .unwrap_or(0);
            if n > max { max = n; }
        }
        self.allday_count = max;
        self.allday_count_date = Some(self.selected_date);
        max
    }

    fn min_slot(&mut self) -> i32 {
        let n = self.allday_count() as i32;
        if n > 0 { -n } else { 0 }
    }

    // =====================================================================
    // Slot navigation
    // =====================================================================

    fn adjust_slot_offset(&mut self) {
        if self.selected_slot < 0 { return; }
        let ac = self.allday_count();
        let extra = if ac > 0 { ac + 1 } else { 0 };
        let available = (self.mid.h as i32 - 3 - extra as i32).max(1);
        let scrolloff = 2;
        if self.selected_slot - self.slot_offset >= available - scrolloff {
            self.slot_offset = (self.selected_slot - available + scrolloff + 1)
                .min((48 - available).max(0));
        } else if self.selected_slot - self.slot_offset < scrolloff {
            self.slot_offset = (self.selected_slot - scrolloff).max(0);
        }
    }

    fn move_slot_down(&mut self) {
        let ms = self.min_slot();
        self.selected_slot = if self.selected_slot >= 47 { ms } else { self.selected_slot + 1 };
        if self.selected_slot == ms { self.slot_offset = 0; }
        self.adjust_slot_offset();
        self.render_mid_pane();
        self.render_bottom_pane();
    }

    fn move_slot_up(&mut self) {
        let ms = self.min_slot();
        if self.selected_slot <= ms {
            self.selected_slot = 47;
            let ac = self.allday_count();
            let extra = if ac > 0 { ac + 1 } else { 0 };
            let available = (self.mid.h as i32 - 3 - extra as i32).max(1);
            self.slot_offset = (48 - available).max(0);
        } else {
            self.selected_slot -= 1;
        }
        self.adjust_slot_offset();
        self.render_mid_pane();
        self.render_bottom_pane();
    }

    fn page_slots_down(&mut self) {
        let ms = self.min_slot();
        self.selected_slot = (self.selected_slot + 10).min(47).max(ms);
        self.adjust_slot_offset();
        self.render_mid_pane();
        self.render_bottom_pane();
    }

    fn page_slots_up(&mut self) {
        let ms = self.min_slot();
        self.selected_slot = (self.selected_slot - 10).max(ms);
        self.adjust_slot_offset();
        self.render_mid_pane();
        self.render_bottom_pane();
    }

    fn go_slot_top(&mut self) {
        self.selected_slot = self.min_slot();
        self.slot_offset = 0;
        self.render_mid_pane();
        self.render_bottom_pane();
    }

    fn go_slot_bottom(&mut self) {
        self.selected_slot = 47;
        let ac = self.allday_count();
        let extra = if ac > 0 { ac + 1 } else { 0 };
        let available = (self.mid.h as i32 - 3 - extra as i32).max(1);
        self.slot_offset = (48 - available).max(0);
        self.render_mid_pane();
        self.render_bottom_pane();
    }

    // =====================================================================
    // Date/event state changes
    // =====================================================================

    fn date_changed(&mut self) {
        self.selected_event_index = 0;
        self.allday_count_date = None;
        self.load_events_for_range();
        // If slot is in all-day area but no event there, jump out
        if self.selected_slot < 0 && self.event_at_selected_slot().is_none() {
            let events = self.events_on_selected_day();
            let tz = local_tz_offset_secs();
            if let Some(first_timed) = events.iter().find(|e| !e.all_day && !is_background_span(e, tz)) {
                let local = first_timed.start_time + tz;
                let (_, _, _, h, m, _) = ts_to_parts(local);
                self.selected_slot = h as i32 * 2 + if m >= 30 { 1 } else { 0 };
            } else {
                self.selected_slot = now_slot();
            }
            self.slot_offset = (self.selected_slot - 5).max(0);
        }
        self.render_all();
    }

    fn safe_date(y: i32, m: u32, d: u32) -> (i32, u32, u32) {
        let m = m.clamp(1, 12);
        let max_d = days_in_month(y, m);
        (y, m, d.min(max_d))
    }

    fn events_on_selected_day(&self) -> Vec<Event> {
        self.events_by_date.get(&self.selected_date).cloned().unwrap_or_default()
    }

    fn event_at_selected_slot(&mut self) -> Option<Event> {
        let events = self.events_on_selected_day();

        if self.selected_slot < 0 {
            let tz = local_tz_offset_secs();
            let ac = self.allday_count();
            let allday: Vec<&Event> = events.iter().filter(|e| e.all_day || is_background_span(e, tz)).collect();
            let idx = ac as i32 - self.selected_slot.abs();
            if idx >= 0 && (idx as usize) < allday.len() {
                return Some(allday[idx as usize].clone());
            }
            return None;
        }

        let hour = self.selected_slot / 2;
        let minute = (self.selected_slot % 2) * 30;
        let (sy, sm, sd) = self.selected_date;
        let tz = local_tz_offset_secs();
        let slot_start = date_to_ts(sy, sm, sd, hour as u32, minute as u32, 0) - tz;
        let slot_end = slot_start + 1800;

        pick_timed_event_at_slot(&events, slot_start, slot_end).cloned()
    }

    fn select_next_event_on_day(&mut self) {
        let events = self.events_on_selected_day();
        if events.is_empty() { return; }
        self.selected_event_index = (self.selected_event_index + 1) % events.len();
        self.render_mid_pane();
        self.render_bottom_pane();
    }

    fn select_prev_event_on_day(&mut self) {
        let events = self.events_on_selected_day();
        if events.is_empty() { return; }
        self.selected_event_index = if self.selected_event_index == 0 {
            events.len() - 1
        } else {
            self.selected_event_index - 1
        };
        self.render_mid_pane();
        self.render_bottom_pane();
    }

    fn move_slot_to_event(&mut self, evt: &Event) {
        let tz = local_tz_offset_secs();
        if evt.all_day || is_background_span(evt, tz) {
            let ac = self.allday_count();
            let events = self.events_on_selected_day();
            let allday: Vec<&Event> = events.iter().filter(|e| e.all_day || is_background_span(e, tz)).collect();
            let idx = allday.iter().position(|e| e.id == evt.id).unwrap_or(0);
            self.selected_slot = -(ac as i32 - idx as i32);
        } else {
            let local = evt.start_time + tz;
            let (_, _, _, h, m, _) = ts_to_parts(local);
            self.selected_slot = h as i32 * 2 + if m >= 30 { 1 } else { 0 };
            self.slot_offset = (self.selected_slot - 5).max(0);
        }
    }

    fn jump_to_next_event(&mut self) {
        let events = self.events_on_selected_day();
        if !events.is_empty() && self.selected_event_index < events.len() - 1 {
            self.selected_event_index += 1;
            let evt = events[self.selected_event_index].clone();
            self.move_slot_to_event(&evt);
            self.render_mid_pane();
            self.render_bottom_pane();
            return;
        }

        for offset in 1..=365 {
            let d = add_days(self.selected_date, offset);
            if let Ok(day_events) = self.db.get_events_for_date(d.0, d.1, d.2) {
                if !day_events.is_empty() {
                    self.selected_date = d;
                    self.selected_event_index = 0;
                    self.allday_count_date = None;
                    self.load_events_for_range();
                    let events = self.events_on_selected_day();
                    if let Some(first) = events.first() {
                        let first = first.clone();
                        self.move_slot_to_event(&first);
                    }
                    self.render_all();
                    return;
                }
            }
        }
        self.show_feedback("No more events found within the next year", 245);
    }

    fn jump_to_prev_event(&mut self) {
        let events = self.events_on_selected_day();
        if !events.is_empty() && self.selected_event_index > 0 {
            self.selected_event_index -= 1;
            let evt = events[self.selected_event_index].clone();
            self.move_slot_to_event(&evt);
            self.render_mid_pane();
            self.render_bottom_pane();
            return;
        }

        for offset in 1..=365 {
            let d = add_days(self.selected_date, -(offset as i32));
            if let Ok(day_events) = self.db.get_events_for_date(d.0, d.1, d.2) {
                if !day_events.is_empty() {
                    self.selected_date = d;
                    self.allday_count_date = None;
                    self.load_events_for_range();
                    let events = self.events_on_selected_day();
                    self.selected_event_index = events.len().saturating_sub(1);
                    if let Some(last) = events.last() {
                        let last = last.clone();
                        self.move_slot_to_event(&last);
                    }
                    self.render_all();
                    return;
                }
            }
        }
        self.show_feedback("No earlier events found within the past year", 245);
    }

    // =====================================================================
    // Data loading
    // =====================================================================

    fn load_events_for_range(&mut self) {
        let (sy, sm, _) = self.selected_date;
        let range_start = add_months((sy, sm, 1), -3);
        let range_end_m = add_months((sy, sm, 1), 3);
        let range_end = (range_end_m.0, range_end_m.1, days_in_month(range_end_m.0, range_end_m.1));

        let tz = local_tz_offset_secs();
        let start_ts = date_to_ts(range_start.0, range_start.1, range_start.2, 0, 0, 0) - tz;
        let end_ts = date_to_ts(range_end.0, range_end.1, range_end.2, 23, 59, 59) - tz;

        let raw_events = self.db.get_events_in_range(start_ts, end_ts).unwrap_or_default();

        self.events_by_date.clear();
        for evt in &raw_events {
            // All-day events are stored as UTC midnight per the iCal/Google/Outlook
            // floating-date convention — they are DATES, not timestamps. Applying a
            // local-TZ shift pushes the (exclusive) end into the next day; don't.
            // Timed events do need the shift so their wall-clock date is right.
            let (sy2, sm2, sd2) = if evt.all_day {
                let (y, m, d, _, _, _) = ts_to_parts(evt.start_time);
                (y, m, d)
            } else {
                let (y, m, d, _, _, _) = ts_to_parts(evt.start_time + tz);
                (y, m, d)
            };
            let (ey, em, ed) = if evt.all_day {
                // Exclusive end → subtract 1 second before extracting the date,
                // so a May 23 → May 28 (exclusive) event ends on May 27.
                let end_ts = if evt.end_time > evt.start_time { evt.end_time - 1 } else { evt.start_time };
                let (y, m, d, _, _, _) = ts_to_parts(end_ts);
                (y, m, d)
            } else {
                let (y, m, d, _, _, _) = ts_to_parts(evt.end_time + tz);
                (y, m, d)
            };

            let mut cur = (sy2, sm2, sd2);
            let end_date = (ey, em, ed);
            loop {
                if cur >= range_start && cur <= range_end {
                    self.events_by_date.entry(cur).or_default().push(evt.clone());
                }
                if cur >= end_date { break; }
                cur = add_days(cur, 1);
                // Safety: don't loop more than 366 days
                if day_diff(cur, (sy2, sm2, sd2)) > 366 { break; }
            }
        }

        // Sort each day's events
        for evts in self.events_by_date.values_mut() {
            evts.sort_by_key(|e| e.start_time);
        }

        // Clamp selected event index
        let events = self.events_on_selected_day();
        if events.is_empty() {
            self.selected_event_index = 0;
        } else if self.selected_event_index >= events.len() {
            self.selected_event_index = events.len() - 1;
        }

        // Load weather (cached)
        let now = database::now_secs();
        if self.weather_forecast.is_empty() || (now - self.weather_fetched_at) > 21600 {
            let lat = self.config.get_f64("location.lat", 59.9139);
            let lon = self.config.get_f64("location.lon", 10.7522);
            self.weather_forecast = weather::fetch_cached(lat, lon, &self.db);
            self.weather_fetched_at = now;
        }

        // Invalidate allday cache
        self.allday_count_date = None;
    }

    // =====================================================================
    // Rendering
    // =====================================================================

    fn render_all(&mut self) {
        // Check for resize
        let (cols, rows) = Crust::terminal_size();
        if cols != self.cols || rows != self.rows {
            Crust::clear_screen();
            self.recreate_panes();
        }

        // Set terminal title
        let events = self.events_on_selected_day();
        let (sy, sm, sd) = self.selected_date;
        let mut title = format!("Tock: {}", format_date_short(sy, sm, sd));
        if !events.is_empty() {
            title.push_str(&format!(" ({} event{})", events.len(),
                if events.len() == 1 { "" } else { "s" }));
        }
        Crust::set_title(&title);

        self.render_info_bar();
        self.render_top_pane();
        self.render_mid_pane();
        self.render_bottom_pane();
        self.render_status_bar();
    }

    // ----- Info bar -----

    fn render_info_bar(&mut self) {
        let (sy, sm, sd) = self.selected_date;
        let title = style::bold(" Tock");
        // tock-event-counter: show count of events on selected day in header.
        let event_count = self.events_on_selected_day().len();
        let date_str = if event_count > 0 {
            format!("  {}  ·  {} event{}",
                format_date_long(sy, sm, sd),
                event_count,
                if event_count == 1 { "" } else { "s" })
        } else {
            format!("  {}", format_date_long(sy, sm, sd))
        };

        let phase = orbit::moon_phase(sy, sm, sd);
        let moon_color = body_color("moon");
        let moon = format!("  {} {} ({}%)",
            style::fg_rgb(phase.symbol, &moon_color), phase.phase_name,
            (phase.illumination * 100.0).round() as i32);

        let lat = self.config.get_f64("location.lat", 59.9139);
        let lon = self.config.get_f64("location.lon", 10.7522);
        let tz = self.config.get_f64("timezone_offset", 1.0);

        // Harmonised header pattern: `<body glyph> <up/down arrow>
        // <time>` for sun AND moon, so both rise/set pairs read the
        // same. One body glyph each, one direction-arrow set across
        // both. The arrows are U+2191 (↑) and U+2193 (↓) which are
        // unambiguously text in every terminal font we care about.
        // VS-15 (U+FE0E) on the body glyphs keeps emoji-presentation
        // renderers from blowing them up to 2-cell colour icons.
        let moon_rs = match orbit::moon_times(sy, sm, sd, lat, lon, tz) {
            Some((rise, set)) => {
                let mc = body_color("moon");
                // ☾ U+263E LAST QUARTER MOON — used as the generic
                // moon body glyph here, neutral on waxing/waning so
                // the symbol describes the body, not its phase.
                format!("  {}\u{2191}{}  {}\u{2193}{}",
                    style::fg_rgb("\u{263E}\u{FE0E}", &mc), rise,
                    style::fg_rgb("\u{263E}\u{FE0E}", &mc), set)
            }
            None => String::new(),
        };
        let sun_str = match orbit::sun_times(sy, sm, sd, lat, lon, tz) {
            Some((rise, set)) => {
                let sc = body_color("sun");
                // ☀ U+2600 BLACK SUN WITH RAYS — same sun for both,
                // arrow tells which is which. Avoids the earlier
                // `☼ + ☀` pair which rendered as `✷ + ☀` in some
                // fonts and didn't read as "matched set".
                format!("  {}\u{2191}{}  {}\u{2193}{}",
                    style::fg_rgb("\u{2600}\u{FE0E}", &sc), rise,
                    style::fg_rgb("\u{2600}\u{FE0E}", &sc), set)
            }
            None => String::new(),
        };

        // Visible planets (cached per date). We override orbit's
        // astrological glyphs with two-letter Latin abbreviations
        // (Me / Ve / Ma / Ju / Sa) so the row reads uniformly in
        // every terminal. Venus and Mars are on Unicode's default-
        // emoji list and many font stacks ignore VS-15 — those two
        // would blow up to 2-cell colour icons next to small-text
        // Mercury / Jupiter / Saturn and the row would never sit
        // flush. Colour from `p.color` still distinguishes them at
        // a glance. Nova / astro keep the orbit glyphs since they
        // render in different contexts.
        if self.cached_planets_date != Some(self.selected_date) {
            let planets = orbit::visible_planets(sy, sm, sd, lat, lon, tz);
            self.cached_planets = planets.iter().map(|p| {
                let abbrev = planet_abbrev(p.name);
                style::fg_rgb(abbrev, p.color)
            }).collect();
            self.cached_planets_date = Some(self.selected_date);
        }
        let planet_str = if !self.cached_planets.is_empty() {
            format!("  {}", self.cached_planets.join(" "))
        } else {
            String::new()
        };

        let text = format!("{}{}{}{}{}{}", title, date_str, moon, moon_rs, sun_str, planet_str);
        self.info.set_text(&text);
        self.info.refresh();
    }

    // ----- Status bar -----

    fn render_status_bar(&mut self) {
        let keys = "d/D:Day  w/W:Week  m/M:Month  y/Y:Year  e/E:Event  J:Join  N:Note  p:Pres  n:New  g:GoTo  t:Today  i:Import  G:Google  O:Outlook  S:Sync  C:Cal  P:Prefs  ?:Help  q:Quit";
        let version = format!("tock v{}", env!("CARGO_PKG_VERSION"));
        let w = self.cols as usize;
        if self.syncing {
            let sync_ind = style::fg(" Syncing...", 226);
            let used = keys.len() + 12 + version.len() + 2;
            let pad_len = w.saturating_sub(used).max(1);
            let text = format!(" {}{}{} {}", keys, " ".repeat(pad_len), sync_ind, version);
            self.status.set_text(&text);
        } else {
            let used = keys.len() + version.len() + 3;
            let pad_len = w.saturating_sub(used).max(1);
            let text = format!(" {}{}{}", keys, " ".repeat(pad_len), version);
            self.status.set_text(&text);
        }
        self.status.refresh();
    }

    // ----- Top pane (mini months) -----

    fn render_top_pane(&mut self) {
        let (sy, sm, sd) = self.selected_date;
        let t = today();
        let month_width = 26usize; // 25 + 1 separator
        // Show only current/next month (2 strips). Subtract to make
        // negative space — Boris-style: don't display info you never use.
        // The past is one `M` away; the quote strip gets the freed columns.
        let months_visible = 2usize;
        let offset = 0; // Selected (current) month is 1st, next=2nd

        let mut month_data: Vec<(i32, u32)> = Vec::new();
        for i in 0..months_visible {
            let m_off = i as i32 - offset as i32;
            let d = add_months((sy, sm, 1), m_off);
            month_data.push((d.0, d.1));
        }

        let current_month_bg = self.config.get_i64("colors.current_month_bg", 233);
        let today_bg = self.config.get_i64("colors.today_bg", 246) as u8;

        let rendered: Vec<Vec<String>> = month_data.iter().map(|&(year, month)| {
            let sel_day = if year == sy && month == sm { Some(sd) } else { None };
            let is_current = year == sy && month == sm;
            let lines = self.render_mini_month(year, month, sel_day, t, today_bg);
            if is_current {
                lines.iter().map(|l| style::bg(l, current_month_bg as u8)).collect()
            } else {
                lines
            }
        }).collect();

        let max_lines = rendered.iter().map(|m| m.len()).max().unwrap_or(0);
        let mut combined: Vec<String> = vec![String::new()]; // 1 row top padding

        for row in 0..max_lines {
            let mut parts: Vec<String> = Vec::new();
            for month_lines in &rendered {
                let line = month_lines.get(row).cloned().unwrap_or_default();
                let pure_len = display_width(&line);
                let pad = (month_width - 1).saturating_sub(pure_len);
                parts.push(format!("{}{}", line, " ".repeat(pad)));
            }
            combined.push(format!(" {}", parts.join(" ")));
        }

        while combined.len() < self.top.h as usize {
            combined.push(String::new());
        }

        // ----- Quote strip — fills the dead space right of the months -----
        // Shows one quote from quotes.file (vault note; `- ` bullets),
        // rotating hourly. Author goes on its own dimmed line (also avoids
        // orphan-word wraps); ·N counter = perfect practice runs (`"` key).
        let quote_x = 1 + months_visible * month_width + 4;
        let avail = (self.cols as usize).saturating_sub(quote_x + 2);
        if avail >= 20 && !self.hide_wall_quote {
            let quotes = load_quotes(&self.quotes_path());
            if !quotes.is_empty() {
                let q = &quotes[quote_index(quotes.len())];
                let (body, author) = split_author(&q.en);
                let wrap_w = avail.saturating_sub(2).min(64);
                let body_fg = self.config.get_i64("quotes.color", 255) as u8;
                let mut qlines: Vec<String> = wrap_display(body, wrap_w)
                    .iter()
                    .enumerate()
                    .map(|(i, l)| {
                        let mark = if i == 0 {
                            style::bold(&style::fg("❝ ", 117))
                        } else {
                            "  ".to_string()
                        };
                        format!("{}{}", mark, style::bold(&style::fg(l, body_fg)))
                    })
                    .collect();
                let n = practice_success_count(&q.en);
                match author {
                    Some(a) => {
                        let mut line = format!("  {}", style::fg(&format!("— {}", a), 242));
                        if n > 0 {
                            line.push_str(&style::fg(&format!("  ·{}", n), 238));
                        }
                        qlines.push(line);
                    }
                    None if n > 0 => {
                        qlines.push(format!("  {}", style::fg(&format!("·{}", n), 238)));
                    }
                    None => {}
                }
                // Small Chinese gloss under the attribution (dimmest layer).
                if let Some(ref zh) = q.zh {
                    for l in wrap_display(zh, wrap_w) {
                        qlines.push(format!("  {}", style::fg(&l, 245)));
                    }
                }
                qlines.truncate(max_lines.max(1));
                let start = 1 + max_lines.saturating_sub(qlines.len()) / 2;
                // Centre the block in the dead space right of the months —
                // on wide terminals a left-hugging quote disappears into the
                // void; hanging it mid-wall makes it readable at a glance.
                let block_w = qlines.iter().map(|l| display_width(l)).max().unwrap_or(0);
                let block_x = quote_x + avail.saturating_sub(block_w) / 2;
                for (i, ql) in qlines.iter().enumerate() {
                    let row = start + i;
                    if row >= combined.len() {
                        break;
                    }
                    let pad = block_x.saturating_sub(display_width(&combined[row]));
                    // bg(0) re-asserts the pane background: the current-month
                    // block ends with a bg reset, which left the quote (and
                    // the gap before it) on the terminal default bg — visible
                    // as an off-colour band behind the text.
                    let segment = style::bg(&format!("{}{}", " ".repeat(pad), ql), 0);
                    combined[row] = format!("{}{}", combined[row], segment);
                }
            }
        }

        self.top.set_text(&combined.join("\n"));
        self.top.full_refresh();
    }

    fn render_mini_month(&self, year: i32, month: u32, sel_day: Option<u32>,
                          today_date: (i32, u32, u32), today_bg: u8) -> Vec<String> {
        let mut lines = Vec::new();

        // Title
        let title = format!("{} {}", month_name(month), year);
        let pad = (25usize.saturating_sub(title.len())) / 2;
        lines.push(format!("{}{}", " ".repeat(pad.max(1)), style::bold(&title)));

        // Weekday header
        let days = ["Mo", "Tu", "We", "Th", "Fr", "Sa", "Su"];
        let hdr: Vec<String> = days.iter().enumerate().map(|(i, d)| {
            let s = format!("{:>2}", d);
            match i {
                5 => style::fg(&s, 208),
                6 => style::fg(&s, 167),
                _ => style::fg(&s, 245),
            }
        }).collect();
        lines.push(format!("    {}", hdr.join(" ")));

        // Build weeks
        let first_wd = cwday(year, month, 1);
        let last_day = days_in_month(year, month);
        let mut week: Vec<Option<u32>> = Vec::new();
        for _ in 0..(first_wd - 1) { week.push(None); }

        for day in 1..=last_day {
            week.push(Some(day));
            if week.len() == 7 {
                lines.push(self.format_mini_week(&week, year, month, sel_day, today_date, today_bg));
                week.clear();
            }
        }
        if !week.is_empty() {
            while week.len() < 7 { week.push(None); }
            lines.push(self.format_mini_week(&week, year, month, sel_day, today_date, today_bg));
        }

        // Pad to 8 lines
        while lines.len() < 8 {
            lines.push(" ".repeat(25));
        }
        lines
    }

    fn format_mini_week(&self, week: &[Option<u32>], year: i32, month: u32,
                         sel_day: Option<u32>, today_date: (i32, u32, u32), today_bg: u8) -> String {
        let first_day = week.iter().flatten().next().copied().unwrap_or(1);
        let wn = cweek(year, month, first_day);
        let wn_str = style::fg(&format!("{:2}", wn), 238);

        let cells: Vec<String> = week.iter().enumerate().map(|(i, day_opt)| {
            match day_opt {
                None => "  ".to_string(),
                Some(day) => {
                    let day = *day;
                    let date = (year, month, day);
                    let is_today = date == today_date;
                    let is_selected = sel_day == Some(day);
                    let events = self.events_by_date.get(&date);
                    let has_events = events.map(|e| !e.is_empty()).unwrap_or(false);

                    let base_color: Option<u8> = if has_events {
                        Some(events.unwrap().first().map(|e| e.calendar_color as u8).unwrap_or(39))
                    } else if i == 6 { // Sunday
                        Some(167)
                    } else if i == 5 { // Saturday
                        Some(208)
                    } else {
                        None
                    };

                    let d = format!("{:2}", day);
                    if is_selected && is_today {
                        let s = if let Some(c) = base_color {
                            style::fg(&d, c)
                        } else { d };
                        style::bg(&style::underline(&style::bold(&s)), today_bg)
                    } else if is_selected {
                        let s = if let Some(c) = base_color {
                            style::fg(&d, c)
                        } else { d };
                        style::underline(&style::bold(&s))
                    } else if is_today {
                        let s = if let Some(c) = base_color {
                            style::fg(&d, c)
                        } else { d };
                        style::bg(&s, today_bg)
                    } else if let Some(c) = base_color {
                        style::fg(&d, c)
                    } else {
                        d
                    }
                }
            }
        }).collect();

        format!("{} {}", wn_str, cells.join(" "))
    }

    // ----- Mid pane (week view) -----

    fn render_mid_pane(&mut self) {
        let (sy, sm, sd) = self.selected_date;
        let wd = cwday(sy, sm, sd);
        let week_start = add_days(self.selected_date, -(wd as i32 - 1));

        let time_col = 6usize; // "HH:MM "
        let gap = 1usize;
        let day_col = ((self.cols as usize).saturating_sub(time_col + gap * 6) / 7).max(8);

        let sel_alt_a = self.config.get_i64("colors.selected_bg_a", 235) as u8;
        let sel_alt_b = self.config.get_i64("colors.selected_bg_b", 234) as u8;
        let alt_bg_a = self.config.get_i64("colors.alt_bg_a", 233) as u8;
        let alt_bg_b = self.config.get_i64("colors.alt_bg_b", 0) as u8;
        let slot_sel_bg = self.config.get_i64("colors.slot_selected_bg", 237) as u8;
        let today_bg = self.config.get_i64("colors.today_bg", 246) as u8;
        let today_fg = self.config.get_i64("colors.today_fg", 232) as u8;
        let sat_color = self.config.get_i64("colors.saturday", 208) as u8;
        let sun_color = self.config.get_i64("colors.sunday", 167) as u8;
        let t = today();
        let tz = local_tz_offset_secs();

        let mut lines: Vec<String> = Vec::new();

        // Weather row
        let mut weather_parts = vec![" ".repeat(time_col)];
        for i in 0..7 {
            let day = add_days(week_start, i);
            let w_str = weather::short_for_date(&self.weather_forecast, day.0, day.1, day.2)
                .unwrap_or_default();
            let pure_len = display_width(&w_str);
            let pad = day_col.saturating_sub(pure_len);
            weather_parts.push(format!("{}{}", style::fg(&w_str, 245), " ".repeat(pad)));
        }
        lines.push(weather_parts.join(" "));

        // Day headers
        let wk = cweek(week_start.0, week_start.1, week_start.2);
        let wk_label = format!("W{}", wk);
        let wk_str = style::fg(&wk_label, 238);
        let wk_pad = time_col.saturating_sub(wk_label.len()).max(1);
        let mut header_parts = vec![format!("{}{}", wk_str, " ".repeat(wk_pad))];

        for i in 0..7 {
            let day = add_days(week_start, i);
            let day_wd = cwday(day.0, day.1, day.2);
            let header_text = format!("{} {}", weekday_short(day_wd), day.2);
            let is_sel = day == self.selected_date;
            let is_today = day == t;

            let base_color: u8 = if day_wd == 7 { sun_color }
                else if day_wd == 6 { sat_color }
                else { 245 };

            let pure_len = header_text.len();
            let pad = day_col.saturating_sub(pure_len);
            let (header, pad_str) = if is_sel && is_today {
                let h = style::bg(&style::fg(&style::underline(&style::bold(&header_text)), today_fg), today_bg);
                (h, style::bg(&" ".repeat(pad), today_bg))
            } else if is_sel {
                let h = style::bg(&style::fg(&style::underline(&style::bold(&header_text)), base_color), sel_alt_a);
                (h, style::bg(&" ".repeat(pad), sel_alt_a))
            } else if is_today {
                let h = style::bg(&style::fg(&style::bold(&header_text), today_fg), today_bg);
                (h, style::bg(&" ".repeat(pad), today_bg))
            } else {
                (style::fg(&header_text, base_color), " ".repeat(pad))
            };
            header_parts.push(format!("{}{}", header, pad_str));
        }
        lines.push(header_parts.join(" "));

        // Separator
        let sep = style::fg(&"-".repeat(self.cols as usize), 238);
        lines.push(sep.clone());

        // All-day events
        let mut week_allday: Vec<Vec<Event>> = Vec::new();
        let mut week_events: Vec<Vec<Event>> = Vec::new();
        for i in 0..7 {
            let day = add_days(week_start, i);
            let all = self.events_by_date.get(&day).cloned().unwrap_or_default();
            // A multi-day "background span" timed event (e.g. a company reminder
            // entered as 6/22 10:00 → 6/30 10:30) fills whole columns in the time
            // grid. Treat it like an all-day event: draw it as a banner bar above
            // the grid, and keep it OUT of the grid below.
            week_allday.push(all.iter().filter(|e| e.all_day || is_background_span(e, tz)).cloned().collect());
            week_events.push(all.iter().filter(|e| !e.all_day && !is_background_span(e, tz)).cloned().collect());
        }

        // Banner lane assignment. Both all-day events and multi-day "background
        // span" timed events (merged into week_allday above) render as horizontal
        // bars here. Give each a STABLE lane across the whole visible week via
        // greedy interval colouring, so a bar spanning several days sits on one
        // row instead of hopping rows per day (which broke run-merging whenever
        // the banner count differed between columns).
        struct Banner { evt: Event, first: usize, last: usize }
        let mut banners: Vec<Banner> = Vec::new();
        {
            let mut seen: std::collections::HashSet<i64> = std::collections::HashSet::new();
            for c in 0..7 {
                for e in &week_allday[c] {
                    if !seen.insert(e.id) { continue; }
                    let mut first = c;
                    let mut last = c;
                    for (cc, day_evts) in week_allday.iter().enumerate() {
                        if day_evts.iter().any(|x| x.id == e.id) {
                            if cc < first { first = cc; }
                            if cc > last { last = cc; }
                        }
                    }
                    banners.push(Banner { evt: e.clone(), first, last });
                }
            }
        }
        banners.sort_by(|a, b| a.first.cmp(&b.first)
            .then(a.evt.start_time.cmp(&b.evt.start_time))
            .then(a.evt.id.cmp(&b.evt.id)));
        let mut lanes_last: Vec<i64> = Vec::new(); // highest col occupied per lane
        let mut lane_of: Vec<usize> = vec![0; banners.len()];
        for (i, b) in banners.iter().enumerate() {
            let mut placed = false;
            for (ln, end) in lanes_last.iter_mut().enumerate() {
                if (b.first as i64) > *end {
                    *end = b.last as i64;
                    lane_of[i] = ln;
                    placed = true;
                    break;
                }
            }
            if !placed {
                lane_of[i] = lanes_last.len();
                lanes_last.push(b.last as i64);
            }
        }
        let max_allday = lanes_last.len();
        // lane_cells[lane][col] = Some(banner index) occupying that cell.
        let mut lane_cells: Vec<[Option<usize>; 7]> = vec![[None; 7]; max_allday];
        for (i, b) in banners.iter().enumerate() {
            for c in b.first..=b.last {
                lane_cells[lane_of[i]][c] = Some(i);
            }
        }
        if max_allday > 0 {
            for row in 0..max_allday {
                let allday_slot = -(max_allday as i32 - row as i32);
                let is_row_selected = self.selected_slot == allday_slot;
                let label = if is_row_selected {
                    format!("{} ", style::bold(&style::fg("  All", 255)))
                } else {
                    " ".repeat(time_col)
                };

                // Runs of consecutive columns sharing the same banner in this
                // lane — a multi-day bar spans one continuous run instead of
                // repeating its title across every cell.
                let cells = &lane_cells[row];
                let mut runs: Vec<(usize, usize, Option<Event>)> = Vec::new();
                let mut c = 0usize;
                while c < 7 {
                    let cur = cells[c].map(|bi| banners[bi].evt.clone());
                    let mut end = c + 1;
                    if let Some(bi) = cells[c] {
                        while end < 7 && cells[end] == Some(bi) { end += 1; }
                    }
                    runs.push((c, end - c, cur));
                    c = end;
                }

                let mut row_str = label;
                let runs_len = runs.len();
                for (run_idx, (start, len, evt)) in runs.iter().enumerate() {
                    let is_last = run_idx == runs_len - 1;
                    // Run width: N cells × day_col + (N-1) inter-cell separators
                    let run_w = *len * day_col + len.saturating_sub(1);

                    let run_has_sel = (*start..(*start + *len)).any(|cc| {
                        add_days(week_start, cc as i32) == self.selected_date
                    });
                    let run_bg = if run_has_sel && is_row_selected {
                        Some(slot_sel_bg)
                    } else if run_has_sel {
                        Some(sel_alt_a)
                    } else {
                        None
                    };

                    let cell_text = if let Some(e) = evt {
                        let title = if e.title.is_empty() { "(No title)" } else { &e.title };
                        let color = e.calendar_color as u8;
                        let marker = if run_has_sel && is_row_selected { ">" } else { " " };
                        let rsvp = rsvp_marker(e.my_status.as_deref());
                        let labeled = if rsvp.is_empty() {
                            title.to_string()
                        } else {
                            format!("{} {}", rsvp, title)
                        };
                        let entry = format!("{}{}", marker, truncate_str(&labeled, run_w.saturating_sub(1)));
                        let pure_len = display_width(&entry);
                        let pad = run_w.saturating_sub(pure_len);
                        let styled = if let Some(bg) = run_bg {
                            style::bg(&style::bold(&style::fg(&entry, color)), bg)
                        } else {
                            style::fg(&entry, color)
                        };
                        let pad_str = if let Some(bg) = run_bg {
                            style::bg(&" ".repeat(pad), bg)
                        } else {
                            " ".repeat(pad)
                        };
                        format!("{}{}", styled, pad_str)
                    } else {
                        // Empty cell (always run length 1; we don't merge None).
                        if let Some(bg) = run_bg {
                            style::bg(&" ".repeat(day_col), bg)
                        } else {
                            " ".repeat(day_col)
                        }
                    };

                    row_str.push_str(&cell_text);
                    if !is_last {
                        row_str.push(' ');
                    }
                }
                lines.push(row_str);
            }
            lines.push(style::fg(&"-".repeat(self.cols as usize), 238));
        }

        // Time grid
        let _work_start = self.config.get_i64("work_hours.start", 8) as i32;
        let extra_rows = if max_allday > 0 { max_allday + 1 } else { 0 };

        // "Now line" — a horizontal indicator showing the current time
        // across the week grid. The day header already highlights today,
        // so we don't need a dot — a clean dash row with the time
        // right-aligned is enough. Only drawn when today is in the
        // visible week. Costs one row of vertical space; budget for it
        // up-front to avoid clipping.
        let today_in_view = (0..7).any(|c| add_days(week_start, c) == t);
        let now_secs_into_today = {
            let today_midnight_utc = date_to_ts(t.0, t.1, t.2, 0, 0, 0) - tz;
            (crate::database::now_secs() - today_midnight_utc).max(0)
        };
        let now_slot_idx = (now_secs_into_today / 1800) as i32;
        let now_hh = (now_secs_into_today / 3600) as i32;
        let now_mm = ((now_secs_into_today % 3600) / 60) as i32;
        let now_line_reserve = if today_in_view { 1 } else { 0 };

        let available = (self.mid.h as i32 - 3 - extra_rows as i32 - now_line_reserve).max(1);

        // Default offset
        if self.slot_offset < 0 { self.slot_offset = 0; }
        let max_offset = (48 - available).max(0);
        if self.slot_offset > max_offset { self.slot_offset = max_offset; }

        let end_slot = (self.slot_offset + available).min(48);
        for slot_idx in self.slot_offset..end_slot {
            let hour = slot_idx / 2;
            let minute = (slot_idx % 2) * 30;
            let row_num = (slot_idx - self.slot_offset) as usize;
            let is_slot_selected = self.selected_slot == slot_idx;
            let row_bg = if row_num % 2 == 0 { alt_bg_a } else { alt_bg_b };

            let time_label = format!("{:02}:{:02} ", hour, minute);
            let tl = if is_slot_selected {
                style::bold(&style::fg(&time_label, 255))
            } else {
                style::fg(&time_label, 238)
            };

            let mut parts = vec![tl];
            for col in 0..7 {
                let day = add_days(week_start, col);
                let is_sel = day == self.selected_date;
                let cell_bg = if is_sel && is_slot_selected {
                    slot_sel_bg
                } else if is_sel {
                    if row_num % 2 == 0 { sel_alt_a } else { sel_alt_b }
                } else {
                    row_bg
                };

                let day_ts_start = date_to_ts(day.0, day.1, day.2,
                    hour as u32, minute as u32, 0) - tz;
                let day_ts_end = day_ts_start + 1800;

                let evt_opt = week_events[col as usize].iter().find(|e| {
                    e.start_time < day_ts_end && e.end_time > day_ts_start
                });

                let cell = if let Some(evt) = evt_opt {
                    let is_at_slot = is_sel && is_slot_selected;
                    let color = evt.calendar_color as u8;
                    // Multi-row title wrap (option 🅔): instead of printing
                    // the title once and leaving the continuation rows as
                    // single-bar empty rows, wrap the title across all rows
                    // the event actually occupies. End time `-HH:MM` lives
                    // on the bottom row, right-aligned. Every row uses the
                    // same `▌` bar so the column reads as one solid block.
                    let day_midnight_ts = date_to_ts(day.0, day.1, day.2, 0, 0, 0) - tz;
                    let event_first_slot = ((evt.start_time - day_midnight_ts).max(0) / 1800) as i32;
                    // -1 because end_time is exclusive; an event ending at
                    // 17:00 finishes IN slot 33 (16:30-17:00), not slot 34.
                    let event_last_slot = (((evt.end_time - 1) - day_midnight_ts).max(0) / 1800) as i32;
                    let visible_first = event_first_slot.max(self.slot_offset);
                    let visible_last = event_last_slot.min(end_slot - 1);
                    let current_event_row = (slot_idx - visible_first).max(0) as usize;
                    let is_last_row = slot_idx == visible_last;
                    let ends_in_view = evt.end_time > day_ts_start
                        && evt.end_time <= (day_midnight_ts + (end_slot as i64) * 1800);

                    // Title text (cached construction across rows).
                    let title = if evt.title.is_empty() { "(No title)" } else { &evt.title };
                    let rsvp = rsvp_marker(evt.my_status.as_deref());
                    let labeled = if rsvp.is_empty() {
                        title.to_string()
                    } else {
                        format!("{} {}", rsvp, title)
                    };

                    // End-time tail only on bottom row, only if the event
                    // actually ends within our viewport.
                    let tail = if is_last_row && ends_in_view {
                        let end_local = evt.end_time + tz;
                        let hh = ((end_local.rem_euclid(86400)) / 3600) as i32;
                        let mm = ((end_local.rem_euclid(3600)) / 60) as i32;
                        format!(" -{:02}:{:02}", hh, mm)
                    } else {
                        String::new()
                    };
                    let tail_w = display_width(&tail);

                    // Per-row title width budget. Layout per row:
                    //   prefix(1) + bar(1) + space(1) + title + pad + tail
                    let row_w = day_col.saturating_sub(3); // base budget per row
                    let title_max_w = if is_last_row {
                        row_w.saturating_sub(tail_w)
                    } else {
                        row_w
                    };
                    let start_w = current_event_row * row_w;
                    let title_slice = slice_by_display(&labeled, start_w, title_max_w);
                    let title_w = display_width(&title_slice);

                    let prefix = if is_at_slot { ">" } else { " " };
                    let bar = style::fg("\u{258C}", color); // ▌
                    let title_styled = if title_slice.is_empty() {
                        String::new()
                    } else {
                        style::bold(&style::fg(&title_slice, 255))
                    };
                    let tail_styled = if tail.is_empty() {
                        String::new()
                    } else {
                        style::fg(&tail, color)
                    };
                    // 3 cells overhead (prefix + bar + space).
                    let used_w = 3 + title_w + tail_w;
                    let pad = day_col.saturating_sub(used_w);
                    let pad_str = if pad > 0 {
                        style::bg(&" ".repeat(pad), cell_bg)
                    } else {
                        String::new()
                    };
                    let entry = format!("{}{} {}{}{}", prefix, bar, title_styled, pad_str, tail_styled);
                    style::bg(&entry, cell_bg)
                } else {
                    style::bg(" ", cell_bg)
                };

                let pure_len = display_width(&cell);
                let pad = day_col.saturating_sub(pure_len);
                parts.push(format!("{}{}", cell, style::bg(&" ".repeat(pad), cell_bg)));
            }
            lines.push(parts.join(" "));

            // Push the "now line" right after the slot containing the
            // current time. Clean dashes across the full pane width with
            // the time right-aligned — the left gutter is dashes too so
            // there's no slot-label-looking text on this row.
            if today_in_view && slot_idx == now_slot_idx {
                let total_w = self.cols as usize;
                let label = format!(" {:02}:{:02}", now_hh, now_mm); // 6 cells incl. leading space
                let label_w = display_width(&label);
                let dashes_w = total_w.saturating_sub(label_w);
                let dashes: String = "─".repeat(dashes_w);
                let raw = format!("{}{}", dashes, label);
                lines.push(style::fg(&raw, 196u8));
            }
        }

        while lines.len() < self.mid.h as usize {
            lines.push(String::new());
        }

        self.mid.set_text(&lines.join("\n"));
        self.mid.full_refresh();
    }

    // ----- Bottom pane -----

    fn render_bottom_pane(&mut self) {
        let mut lines: Vec<String> = Vec::new();
        let (sy, sm, sd) = self.selected_date;
        let events = self.events_on_selected_day();
        let w = self.cols as usize;

        // Separator
        lines.push(style::fg(&"-".repeat(w), 238));

        let evt = self.event_at_selected_slot();
        if let Some(evt) = evt {
            let color = evt.calendar_color as u8;
            let title_only = if evt.title.is_empty() { "(No title)".to_string() } else { evt.title.clone() };
            let rsvp = rsvp_marker(evt.my_status.as_deref());
            let title = if rsvp.is_empty() { title_only } else { format!("{} {}", rsvp, title_only) };
            let tz = local_tz_offset_secs();

            // tock-event-counter: show current event's position in the day's
            // event list, e.g. "[3/5]". Suppressed when there's only 1 event.
            let total_events = events.len();
            let position = events.iter().position(|e| e.id == evt.id).map(|i| i + 1);
            let counter = match position {
                Some(p) if total_events > 1 => format!("  [{}/{}]", p, total_events),
                _ => String::new(),
            };

            let time_info = if evt.all_day {
                format!("{}-{:02}-{:02}  All day{}", sy, sm, sd, counter)
            } else {
                let local_s = evt.start_time + tz;
                let (_, _, _, sh, smn, _) = ts_to_parts(local_s);
                let local_e = evt.end_time + tz;
                let (_, _, _, eh, emn, _) = ts_to_parts(local_e);
                let swd = cwday(sy, sm, sd);
                format!("{} {}-{:02}-{:02}  {:02}:{:02} - {:02}:{:02}{}",
                    weekday_short(swd), sy, sm, sd, sh, smn, eh, emn, counter)
            };

            lines.push(format!(" {}  {}",
                style::bold(&style::fg(&title, color)),
                style::fg(&time_info, 252)));

            // Details line
            let mut details: Vec<String> = Vec::new();
            if let Some(ref loc) = evt.location {
                let loc = loc.trim();
                if !loc.is_empty() { details.push(format!("Location: {}", loc)); }
            }
            if let Some(ref org) = evt.organizer {
                let org = org.trim();
                if !org.is_empty() { details.push(format!("Organizer: {}", org)); }
            }
            details.push(format!("Calendar: {}", evt.calendar_name));
            let detail_line = format!(" {}", details.join("  |  "));
            let detail_line = truncate_str(&detail_line, w.saturating_sub(2));
            lines.push(style::fg(&detail_line, 245));

            // Status
            let mut status_parts: Vec<String> = Vec::new();
            if !evt.status.is_empty() {
                status_parts.push(format!("Status: {}", evt.status));
            }
            if let Some(ref ms) = evt.my_status {
                status_parts.push(format!("My status: {}", humanize_status(ms)));
            }
            if !status_parts.is_empty() {
                lines.push(style::fg(&format!(" {}", status_parts.join("  |  ")), 245));
            }

            // Description
            if let Some(ref desc) = evt.description {
                let desc = clean_description(desc);
                if !desc.is_empty() {
                    let desc_flat = desc.replace('\n', " ").replace('\r', "");
                    lines.push(String::new());
                    let max_lines = 50;
                    let mut line = " ".to_string();
                    for word in desc_flat.split_whitespace() {
                        if line.len() + word.len() + 1 > w.saturating_sub(2) {
                            lines.push(style::fg(&line, 248));
                            if lines.len() >= max_lines { break; }
                            line = format!(" {}", word);
                        } else {
                            if line == " " {
                                line.push_str(word);
                            } else {
                                line.push(' ');
                                line.push_str(word);
                            }
                        }
                    }
                    if lines.len() < max_lines && line.trim().len() > 0 {
                        lines.push(style::fg(&line, 248));
                    }
                }
            }
        } else {
            // Day summary
            lines.push(style::bold(&format!(" {}", format_date_long(sy, sm, sd))));

            // Astronomical events
            let astro = orbit::astro_events_for_year(sy, sm, sd);
            for a in &astro {
                lines.push(style::fg(&format!(" {}", a), 180));
            }

            lines.push(String::new());
            if !events.is_empty() {
                let allday = events.iter().filter(|e| e.all_day).count();
                let timed = events.len() - allday;
                let mut parts: Vec<String> = Vec::new();
                if timed > 0 { parts.push(format!("{} timed", timed)); }
                if allday > 0 { parts.push(format!("{} all-day", allday)); }
                let plural = if events.len() == 1 { "" } else { "s" };
                lines.push(style::fg(&format!(" {} event{} today", parts.join(", "), plural), 240));
            } else {
                lines.push(style::fg(" No events scheduled", 240));
            }
        }

        while lines.len() < self.bottom.h as usize {
            lines.push(String::new());
        }

        self.bottom.set_text(&lines.join("\n"));
        self.bottom.full_refresh();
    }

    // =====================================================================
    // Input handling
    // =====================================================================

    fn handle_input(&mut self, key: &str) {
        match key {
            "y" => {
                let (y, m, d) = self.selected_date;
                self.selected_date = Self::safe_date(y + 1, m, d);
                self.date_changed();
            }
            "Y" => {
                let (y, m, d) = self.selected_date;
                self.selected_date = Self::safe_date(y - 1, m, d);
                self.date_changed();
            }
            "m" => {
                self.selected_date = add_months(self.selected_date, 1);
                self.date_changed();
            }
            "M" => {
                self.selected_date = add_months(self.selected_date, -1);
                self.date_changed();
            }
            "w" => {
                self.selected_date = add_days(self.selected_date, 7);
                self.date_changed();
            }
            "W" => {
                self.selected_date = add_days(self.selected_date, -7);
                self.date_changed();
            }
            "d" | "l" | "RIGHT" => {
                self.selected_date = add_days(self.selected_date, 1);
                self.date_changed();
            }
            "D" | "h" | "LEFT" => {
                self.selected_date = add_days(self.selected_date, -1);
                self.date_changed();
            }
            "DOWN" => self.move_slot_down(),
            "UP" => self.move_slot_up(),
            "PgDOWN" => self.page_slots_down(),
            "PgUP" => self.page_slots_up(),
            "HOME" => self.go_slot_top(),
            "END" => self.go_slot_bottom(),
            "j" => self.select_next_event_on_day(),
            "k" => self.select_prev_event_on_day(),
            "e" => self.jump_to_next_event(),
            "E" => self.jump_to_prev_event(),
            "t" => {
                self.selected_date = today();
                self.selected_event_index = 0;
                self.selected_slot = now_slot();
                self.slot_offset = (self.selected_slot - 5).max(0);
                self.date_changed();
            }
            "g" => self.go_to_date(),
            "/" => self.search_events(),
            "\"" => self.practice_quote(),
            "n" => self.create_event(),
            "ENTER" => self.edit_event(),
            "x" | "DEL" => self.delete_event(),
            "C-Y" => self.copy_event_to_clipboard(),
            "v" => self.view_event_popup(),
            "a" => self.accept_invite(),
            "A" => self.decline_invite(),
            "T" => self.tentative_invite(),
            "F" => self.show_free_busy(),
            "J" => self.join_meeting(),
            "N" => self.open_meeting_note(),
            "p" => self.open_presentation(),
            "r" => self.reply_via_kastrup(),
            "i" => self.import_ics_file(),
            "G" => self.setup_google_calendar(),
            "O" => self.setup_outlook_calendar(),
            "S" => self.manual_sync(),
            "C" => self.show_calendars(),
            "C-R" => {
                self.cached_planets_date = None;
                self.weather_forecast.clear();
                self.weather_fetched_at = 0;
                self.load_events_for_range();
                self.render_all();
            }
            "C-L" => {
                Crust::clear_screen();
                self.recreate_panes();
                self.render_all();
            }
            "P" => self.show_preferences(),
            "?" => self.show_help(),
            "q" => self.running = false,
            "RESIZE" => {
                Crust::clear_screen();
                self.recreate_panes();
                self.render_all();
            }
            _ => {}
        }
    }

    // =====================================================================
    // Actions
    // =====================================================================

    fn go_to_date(&mut self) {
        self.blank_bottom("");
        let input = self.bottom_ask("Go to: ", "");
        if input.is_empty() { self.render_all(); return; }

        let input = input.trim().to_string();
        if let Some(parsed) = self.parse_go_to_input(&input) {
            self.selected_date = parsed;
            self.selected_event_index = 0;
            self.date_changed();
        } else {
            self.show_feedback(&format!("Could not parse date: {}", input), 196);
        }
    }

    fn parse_go_to_input(&self, input: &str) -> Option<(i32, u32, u32)> {
        let lower = input.to_lowercase();
        if lower == "today" { return Some(today()); }

        // yyyy-mm-dd
        if input.len() >= 8 && input.contains('-') {
            let parts: Vec<&str> = input.split('-').collect();
            if parts.len() == 3 {
                let y: i32 = parts[0].parse().ok()?;
                let m: u32 = parts[1].parse().ok()?;
                let d: u32 = parts[2].parse().ok()?;
                if m >= 1 && m <= 12 && d >= 1 && d <= days_in_month(y, m) {
                    return Some((y, m, d));
                }
            }
        }

        // yyyymmdd (8-digit, no separator)
        if input.len() == 8 && input.chars().all(|c| c.is_ascii_digit()) {
            let y: i32 = input[0..4].parse().ok()?;
            let m: u32 = input[4..6].parse().ok()?;
            let d: u32 = input[6..8].parse().ok()?;
            if m >= 1 && m <= 12 && d >= 1 && d <= days_in_month(y, m) {
                return Some((y, m, d));
            }
        }

        // mmdd (4-digit, current selected year). Falls through to year-only
        // when month/day are out of range (e.g. 2026 → year, not month=20).
        if input.len() == 4 && input.chars().all(|c| c.is_ascii_digit()) {
            let m: u32 = input[0..2].parse().ok()?;
            let d: u32 = input[2..4].parse().ok()?;
            let (sy, _, _) = self.selected_date;
            if m >= 1 && m <= 12 && d >= 1 && d <= days_in_month(sy, m) {
                return Some((sy, m, d));
            }
        }

        // Year only
        if input.len() == 4 {
            if let Ok(y) = input.parse::<i32>() {
                return Some((y, 1, 1));
            }
        }

        // Month name
        let months = ["jan", "feb", "mar", "apr", "may", "jun",
                       "jul", "aug", "sep", "oct", "nov", "dec"];
        for (i, m) in months.iter().enumerate() {
            if lower.starts_with(m) {
                let (sy, _, _) = self.selected_date;
                return Some((sy, (i + 1) as u32, 1));
            }
        }

        // Day number
        if let Ok(d) = input.parse::<u32>() {
            if d >= 1 && d <= 31 {
                let (sy, sm, _) = self.selected_date;
                let max_d = days_in_month(sy, sm);
                return Some((sy, sm, d.min(max_d)));
            }
        }

        None
    }

    /// If `cal` is a remote-source calendar (google / outlook), push the
    /// just-saved event up. For new events (no external_id yet), the
    /// remote create returns an id which we persist back. Returns true
    /// when a remote push happened (success or attempted), false when
    /// the calendar is local-only.
    fn push_event_remote(&mut self, cal: &crate::database::Calendar,
                          local_id: i64, mut data: EventData) -> bool {
        match cal.source_type.as_str() {
            "google" => {
                let cfg_str = match &cal.source_config { Some(s) => s.clone(), None => return true };
                let cfg: serde_json::Value = match serde_json::from_str(&cfg_str) {
                    Ok(v) => v, Err(_) => return true,
                };
                let email = cfg.get("email").and_then(|v| v.as_str()).unwrap_or("");
                let safe_dir = cfg.get("safe_dir").and_then(|v| v.as_str());
                let google_cal_id = cfg.get("google_calendar_id").and_then(|v| v.as_str()).unwrap_or("");
                if email.is_empty() || google_cal_id.is_empty() {
                    self.show_feedback("Google config incomplete (email/google_calendar_id)",
                        214);
                    return true;
                }
                let mut gc = crate::sources::google::GoogleCalendar::new(email, safe_dir);
                if gc.get_access_token().is_none() {
                    self.show_feedback("Google auth failed - run S to re-auth", 196);
                    return true;
                }
                if let Some(ref existing_id) = data.external_id.clone() {
                    // UPDATE existing remote event
                    gc.update_event(google_cal_id, existing_id, &data);
                } else {
                    // CREATE new remote event; persist returned id back locally.
                    if let Some(remote_id) = gc.create_event(google_cal_id, &data) {
                        data.id = Some(local_id);
                        data.external_id = Some(remote_id);
                        let _ = self.db.save_event(&data);
                    } else {
                        self.show_feedback(
                            &format!("Saved locally, Google push failed: {}",
                                gc.last_error.as_deref().unwrap_or("unknown")),
                            196);
                    }
                }
                true
            }
            "outlook" => {
                // Outlook write-back not yet wired; warn user.
                self.show_feedback("Saved locally; Outlook write-back not implemented",
                    214);
                true
            }
            _ => false, // local calendar - no remote action
        }
    }

    /// Mirror of push_event_remote for delete: if the calendar is remote
    /// and we have an external id, delete it on the remote side.
    fn delete_event_remote(&mut self, cal: &crate::database::Calendar,
                            external_id: &str) {
        match cal.source_type.as_str() {
            "google" => {
                let cfg_str = match &cal.source_config { Some(s) => s.clone(), None => return };
                let cfg: serde_json::Value = match serde_json::from_str(&cfg_str) {
                    Ok(v) => v, Err(_) => return,
                };
                let email = cfg.get("email").and_then(|v| v.as_str()).unwrap_or("");
                let safe_dir = cfg.get("safe_dir").and_then(|v| v.as_str());
                let google_cal_id = cfg.get("google_calendar_id").and_then(|v| v.as_str()).unwrap_or("");
                if email.is_empty() || google_cal_id.is_empty() { return; }
                let mut gc = crate::sources::google::GoogleCalendar::new(email, safe_dir);
                if gc.get_access_token().is_none() { return; }
                let _ = gc.delete_event(google_cal_id, external_id);
            }
            _ => {}
        }
    }

    fn create_event(&mut self) {
        let (sy, sm, sd) = self.selected_date;
        let default_time = if self.selected_slot >= 0 {
            format!("{:02}:{:02}", self.selected_slot / 2, (self.selected_slot % 2) * 30)
        } else {
            "09:00".to_string()
        };

        let calendars = self.db.get_calendars(false).unwrap_or_default();
        let default_cal_id = self.config.get_i64("default_calendar", 1);
        let cal = calendars.iter().find(|c| c.id == default_cal_id)
            .or(calendars.first());
        let cal = match cal {
            Some(c) => c.clone(),
            None => { self.show_feedback("No calendars configured", 196); return; }
        };
        let mut cal_id = cal.id;
        let mut cal_color = cal.color as u8;

        // Calendar picker
        if calendars.len() > 1 {
            let cal_list: String = calendars.iter().enumerate()
                .map(|(i, c)| format!("{}:{}", i + 1, c.name))
                .collect::<Vec<_>>().join("  ");
            let default_idx = calendars.iter().position(|c| c.id == cal_id).unwrap_or(0);
            self.blank_bottom(&style::bold(&style::fg(" New Event", cal_color)));
            let pick = self.bottom_ask(&format!(" Calendar ({}): ", cal_list),
                &format!("{}", default_idx + 1));
            if pick.is_empty() { self.render_all(); return; }
            if let Ok(idx) = pick.trim().parse::<usize>() {
                if idx >= 1 && idx <= calendars.len() {
                    cal_id = calendars[idx - 1].id;
                    cal_color = calendars[idx - 1].color as u8;
                }
            }
        }

        self.blank_bottom(&style::bold(&style::fg(
            &format!(" New Event on {}", format_date_long(sy, sm, sd)), cal_color)));
        let title = self.bottom_ask(" Title: ", "");
        if title.trim().is_empty() { self.render_all(); return; }
        let title = title.trim().to_string();

        self.blank_bottom(&style::bold(&style::fg(&format!(" {}", title), cal_color)));
        let time_str = self.bottom_ask(" Start time (HH:MM or 'all day'): ", &default_time);
        if time_str.is_empty() { self.render_all(); return; }

        let all_day = time_str.trim().to_lowercase() == "all day";
        let tz = local_tz_offset_secs();

        let (start_ts, end_ts) = if all_day {
            let s = date_to_ts(sy, sm, sd, 0, 0, 0) - tz;
            (s, s + 86400)
        } else {
            let parts: Vec<&str> = time_str.trim().split(':').collect();
            let hour: u32 = parts.first().and_then(|p| p.parse().ok()).unwrap_or(9);
            let minute: u32 = parts.get(1).and_then(|p| p.parse().ok()).unwrap_or(0);
            let s = date_to_ts(sy, sm, sd, hour, minute, 0) - tz;

            self.blank_bottom(&style::bold(&style::fg(
                &format!(" {} at {}", title, time_str.trim()), cal_color)));
            let dur_str = self.bottom_ask(" Duration in minutes: ", "60");
            if dur_str.is_empty() { self.render_all(); return; }
            let duration: i64 = dur_str.trim().parse().unwrap_or(60).max(1);
            (s, s + duration * 60)
        };

        // Location
        self.blank_bottom(&style::bold(&style::fg(&format!(" {}", title), cal_color)));
        let location = self.bottom_ask(" Location (Enter to skip): ", "");
        let location = if location.trim().is_empty() { None } else { Some(location.trim().to_string()) };

        // Invitees
        self.blank_bottom(&style::bold(&style::fg(&format!(" {}", title), cal_color)));
        let invitees_str = self.bottom_ask(" Invite (comma-separated emails, Enter to skip): ", "");
        let attendees = if invitees_str.trim().is_empty() {
            None
        } else {
            let arr: Vec<serde_json::Value> = invitees_str.split(',')
                .map(|e| serde_json::json!({"email": e.trim()}))
                .collect();
            Some(serde_json::Value::Array(arr))
        };

        // Description
        self.blank_bottom(&style::bold(&style::fg(&format!(" {}", title), cal_color)));
        let desc_str = self.bottom_ask(" Description (Enter to skip): ", "");
        let description = if desc_str.trim().is_empty() {
            None
        } else {
            Some(desc_str.trim().to_string())
        };

        let data = EventData {
            id: None,
            calendar_id: cal_id,
            external_id: None,
            title: title.clone(),
            description,
            location,
            start_time: start_ts,
            end_time: end_ts,
            all_day,
            timezone: None,
            recurrence_rule: None,
            series_master_id: None,
            status: "confirmed".to_string(),
            organizer: None,
            attendees,
            my_status: None,
            alarms: None,
            metadata: None,
        };

        let local_id = match self.db.save_event(&data) {
            Ok(id) => id,
            Err(e) => {
                self.show_feedback(&format!("Save failed: {}", e), 196);
                return;
            }
        };

        // Push to remote source if applicable (Google / Outlook).
        let pushed = self.push_event_remote(&cal, local_id, data);

        self.load_events_for_range();
        self.render_all();
        let suffix = if pushed { " (synced)" } else { "" };
        self.show_feedback(&format!("Event created: {}{}", title, suffix), cal_color);
    }

    fn edit_event(&mut self) {
        let evt = match self.event_at_selected_slot() {
            Some(e) => e,
            None => { self.show_feedback("No event at this time slot", 245); return; }
        };

        self.blank_bottom(&style::bold(" Edit Event"));
        let new_title = self.bottom_ask(" Title: ", &evt.title);
        if new_title.is_empty() { self.render_all(); return; }

        let data = EventData {
            id: Some(evt.id),
            calendar_id: evt.calendar_id,
            external_id: evt.external_id.clone(),
            title: new_title.trim().to_string(),
            description: evt.description.clone(),
            location: evt.location.clone(),
            start_time: evt.start_time,
            end_time: evt.end_time,
            all_day: evt.all_day,
            timezone: evt.timezone.clone(),
            recurrence_rule: evt.recurrence_rule.clone(),
            series_master_id: evt.series_master_id,
            status: evt.status.clone(),
            organizer: evt.organizer.clone(),
            attendees: evt.attendees.clone(),
            my_status: evt.my_status.clone(),
            alarms: evt.alarms.clone(),
            metadata: evt.metadata.clone(),
        };

        let local_id = match self.db.save_event(&data) {
            Ok(id) => id,
            Err(e) => {
                self.show_feedback(&format!("Save failed: {}", e), 196);
                return;
            }
        };

        // Push update to remote if the calendar is a remote source.
        let cal_opt = self.db.get_calendars(false).ok()
            .and_then(|cs| cs.into_iter().find(|c| c.id == evt.calendar_id));
        let pushed = if let Some(cal) = cal_opt {
            self.push_event_remote(&cal, local_id, data)
        } else { false };

        self.load_events_for_range();
        self.render_all();
        let suffix = if pushed { " (synced)" } else { "" };
        self.show_feedback(&format!("Event updated{}", suffix), 156);
    }

    fn delete_event(&mut self) {
        let evt = match self.event_at_selected_slot() {
            Some(e) => e,
            None => { self.show_feedback("No event at this time slot", 245); return; }
        };

        // Is this part of a recurring series? Either it's the master
        // (recurrence_rule set) or an expanded occurrence (series_master_id set).
        let is_series = evt.recurrence_rule.as_ref().map(|r| !r.is_empty()).unwrap_or(false)
            || evt.series_master_id.is_some();

        self.blank_bottom(&style::bold(" Delete Event"));
        if is_series {
            let choice = self.bottom_ask(
                &format!(" Delete '{}': (o)ccurrence / (s)eries / (n)o: ", evt.title),
                "",
            );
            match choice.trim().to_lowercase().as_str() {
                "o" | "occurrence" => {
                    let _ = self.db.delete_event(evt.id);
                    self.load_events_for_range();
                    self.render_all();
                    self.show_feedback("Occurrence deleted", 156);
                }
                "s" | "series" => {
                    match self.db.delete_event_series(evt.id) {
                        Ok(n) => {
                            self.load_events_for_range();
                            self.render_all();
                            self.show_feedback(&format!("Series deleted ({} row(s))", n), 156);
                        }
                        Err(e) => {
                            self.render_all();
                            self.show_feedback(&format!("Delete failed: {}", e), 196);
                        }
                    }
                }
                _ => { self.render_all(); self.show_feedback("Cancelled", 245); }
            }
            return;
        }

        let confirm = self.bottom_ask(&format!(" Delete '{}'? (y/n): ", evt.title), "");
        if confirm.trim().to_lowercase() != "y" { self.render_all(); return; }

        // Push delete to remote first (before we lose the external_id).
        let cal_opt = self.db.get_calendars(false).ok()
            .and_then(|cs| cs.into_iter().find(|c| c.id == evt.calendar_id));
        if let (Some(cal), Some(ref ext)) = (cal_opt, evt.external_id.as_ref()) {
            self.delete_event_remote(&cal, ext);
        }

        let _ = self.db.delete_event(evt.id);
        self.load_events_for_range();
        self.render_all();
        self.show_feedback("Event deleted", 156);
    }

    fn copy_event_to_clipboard(&mut self) {
        let evt = match self.event_at_selected_slot() {
            Some(e) => e,
            None => { self.show_feedback("No event at this time slot", 245); return; }
        };

        let (sy, sm, sd) = self.selected_date;
        let tz = local_tz_offset_secs();
        let mut text_lines: Vec<String> = Vec::new();
        text_lines.push(evt.title.clone());

        if evt.all_day {
            text_lines.push(format!("{}  All day", format_date_long(sy, sm, sd)));
        } else {
            let local_s = evt.start_time + tz;
            let (_, _, _, sh, smn, _) = ts_to_parts(local_s);
            let local_e = evt.end_time + tz;
            let (_, _, _, eh, emn, _) = ts_to_parts(local_e);
            text_lines.push(format!("{}  {:02}:{:02} - {:02}:{:02}",
                format_date_long(sy, sm, sd), sh, smn, eh, emn));
        }

        if let Some(ref loc) = evt.location {
            if !loc.trim().is_empty() { text_lines.push(format!("Location: {}", loc.trim())); }
        }
        if let Some(ref org) = evt.organizer {
            if !org.trim().is_empty() { text_lines.push(format!("Organizer: {}", org.trim())); }
        }
        text_lines.push(format!("Calendar: {}", evt.calendar_name));
        if let Some(ref ms) = evt.my_status {
            text_lines.push(format!("My status: {}", humanize_status(ms)));
        }
        if let Some(ref desc) = evt.description {
            let desc = clean_description(desc);
            if !desc.is_empty() {
                text_lines.push(String::new());
                text_lines.push(desc);
            }
        }

        let text = text_lines.join("\n");
        crust::clipboard_copy(&text, "clipboard");
        crust::clipboard_copy(&text, "primary");
        self.show_feedback("Event copied to clipboard", 156);
    }

    fn view_event_popup(&mut self) {
        let evt = match self.event_at_selected_slot() {
            Some(e) => e,
            None => { self.show_feedback("No event at this time slot", 245); return; }
        };

        let pw = (self.cols.saturating_sub(10) as usize).min(80).max(50) as u16;
        let ph = (self.rows.saturating_sub(6) as usize).min(30) as u16;
        let px = (self.cols.saturating_sub(pw)) / 2;
        let py = (self.rows.saturating_sub(ph)) / 2;

        let mut popup = Pane::new(px, py, pw, ph, 252, 0);
        popup.border = true;
        popup.scroll = true;

        let (sy, sm, sd) = self.selected_date;
        let color = evt.calendar_color as u8;
        let tz = local_tz_offset_secs();
        let mut lines: Vec<String> = Vec::new();

        lines.push(String::new());
        let title = if evt.title.is_empty() { "(No title)" } else { &evt.title };
        lines.push(format!("  {}", style::bold(&style::fg(title, color))));
        lines.push(String::new());

        let when_label = style::fg("When:", 51);
        if evt.all_day {
            lines.push(format!("  {}  {}  All day",
                when_label, format_date_long(sy, sm, sd)));
        } else {
            let local_s = evt.start_time + tz;
            let (_, _, _, sh, smn, _) = ts_to_parts(local_s);
            let local_e = evt.end_time + tz;
            let (_, _, _, eh, emn, _) = ts_to_parts(local_e);
            lines.push(format!("  {}      {}  {:02}:{:02} - {:02}:{:02}",
                when_label, format_date_long(sy, sm, sd), sh, smn, eh, emn));
        }

        if let Some(ref loc) = evt.location {
            if !loc.trim().is_empty() {
                lines.push(format!("  {}  {}", style::fg("Location:", 51), loc.trim()));
            }
        }
        if let Some(ref org) = evt.organizer {
            if !org.trim().is_empty() {
                lines.push(format!("  {} {}", style::fg("Organizer:", 51), org.trim()));
            }
        }
        lines.push(format!("  {}  {}", style::fg("Calendar:", 51), evt.calendar_name));

        let mut status_parts: Vec<String> = Vec::new();
        if !evt.status.is_empty() { status_parts.push(format!("Status: {}", evt.status)); }
        if let Some(ref ms) = evt.my_status {
            status_parts.push(format!("My status: {}", humanize_status(ms)));
        }
        if !status_parts.is_empty() {
            lines.push(style::fg(&format!("  {}", status_parts.join("  |  ")), 245));
        }

        // Attendees
        if let Some(ref att) = evt.attendees {
            if let Some(arr) = att.as_array() {
                if !arr.is_empty() {
                    lines.push(String::new());
                    lines.push(format!("  {}", style::fg("Attendees:", 51)));
                    for a in arr {
                        let name = a.get("name").or(a.get("email")).or(a.get("displayName"))
                            .and_then(|v| v.as_str()).unwrap_or("?");
                        let status = a.get("status").or(a.get("responseStatus"))
                            .and_then(|v| v.as_str()).unwrap_or("");
                        let status_str = if status.is_empty() { String::new() }
                            else { style::fg(&format!("  ({})", status), 245) };
                        lines.push(format!("    {}{}", style::fg(name, 252), status_str));
                    }
                }
            }
        }

        // Description
        if let Some(ref desc) = evt.description {
            let desc = clean_description(desc);
            if !desc.is_empty() {
                lines.push(String::new());
                let sep_w = (pw as usize).saturating_sub(6).max(1);
                lines.push(format!("  {}", style::fg(&"-".repeat(sep_w), 238)));
                for dline in desc.split('\n') {
                    let mut remaining = dline.to_string();
                    let max_w = pw as usize - 6;
                    // Fix: use char-based slicing for multi-byte (CJK) safety
                    while remaining.chars().count() > max_w {
                        let split_at = remaining
                            .char_indices()
                            .nth(max_w)
                            .map(|(i, _)| i)
                            .unwrap_or(remaining.len());
                        lines.push(style::fg(&format!("  {}", &remaining[..split_at]), 248));
                        remaining = remaining[split_at..].to_string();
                    }
                    lines.push(style::fg(&format!("  {}", remaining), 248));
                }
            }
        }

        lines.push(String::new());
        lines.push(format!("  {}", style::fg("UP/DOWN:scroll  C-Y:copy  ESC/q:close", 245)));

        popup.set_text(&lines.join("\n"));
        popup.refresh();

        loop {
            let k = Input::getchr(None);
            match k.as_deref() {
                Some("ESC") | Some("q") | Some("v") => break,
                Some("DOWN") | Some("j") => popup.linedown(),
                Some("UP") | Some("k") => popup.lineup(),
                Some("PgDOWN") => popup.pagedown(),
                Some("PgUP") => popup.pageup(),
                Some("C-Y") => {
                    let clean: Vec<String> = lines.iter()
                        .map(|l| strip_ansi(l)).collect();
                    let text = clean.join("\n");
                    crust::clipboard_copy(&text, "clipboard");
                    crust::clipboard_copy(&text, "primary");
                    if let Some(last) = lines.last_mut() {
                        *last = format!("  {}", style::fg("Copied to clipboard", 156));
                    }
                    popup.set_text(&lines.join("\n"));
                    popup.refresh();
                }
                _ => {}
            }
        }

        Crust::clear_screen();
        self.recreate_panes();
        self.render_all();
    }

    #[allow(dead_code)]
    fn accept_invite(&mut self)    { self.rsvp_invite("accept"); }
    fn decline_invite(&mut self)   { self.rsvp_invite("decline"); }
    fn tentative_invite(&mut self) { self.rsvp_invite("tentative"); }

    /// Update the local RSVP state AND notify the organizer via the
    /// calendar backend when possible. Currently propagates for Outlook
    /// (Microsoft Graph `/me/events/{id}/{accept|decline|tentativelyAccept}`);
    /// Google and local calendars only update the local my_status for now.
    fn rsvp_invite(&mut self, response: &str) {
        let evt = match self.event_at_selected_slot() {
            Some(e) => e,
            None => { self.show_feedback("No event at this time slot", 245); return; }
        };

        let (verb_ing, my_status_value) = match response {
            "accept"    => ("Accepting",  "accepted"),
            "decline"   => ("Declining",  "declined"),
            "tentative" => ("Tentatively accepting", "tentativelyAccepted"),
            _ => { self.show_feedback(&format!("Unknown RSVP: {}", response), 196); return; }
        };
        self.show_feedback(&format!("{} '{}'...", verb_ing, evt.title), 226);

        // Resolve the calendar so we know which backend to talk to.
        let cal_source_type = self.db.get_calendars(false).ok()
            .and_then(|cals| cals.into_iter().find(|c| c.id == evt.calendar_id))
            .map(|c| (c.source_type, c.source_config));

        let mut graph_ok = None::<bool>;
        if let Some((ref stype, Some(ref cfg_str))) = cal_source_type {
            if stype == "outlook" {
                if let Ok(config) = serde_json::from_str::<serde_json::Value>(cfg_str) {
                    let mut oc = crate::sources::outlook::OutlookCalendar::new(&config);
                    if oc.refresh_access_token().is_some() {
                        if let Some(ref ext) = evt.external_id {
                            graph_ok = Some(oc.respond_to_event(ext, response));
                        } else {
                            graph_ok = Some(false);
                        }
                    } else {
                        graph_ok = Some(false);
                    }
                }
            } else if stype == "google" {
                // Google Calendar RSVP: PATCH the event with the user's
                // updated responseStatus and `sendUpdates=all` so the
                // organizer's mail client sees the reply. The user's
                // identity for this calendar lives in source_config.email;
                // the actual calendar id (usually identical) is in
                // google_calendar_id.
                if let Ok(config) = serde_json::from_str::<serde_json::Value>(cfg_str) {
                    let email = config.get("email").and_then(|v| v.as_str()).unwrap_or("");
                    let cal_id = config.get("google_calendar_id")
                        .and_then(|v| v.as_str())
                        .unwrap_or(email);
                    let safe_dir = config.get("safe_dir").and_then(|v| v.as_str());
                    if !email.is_empty() && !cal_id.is_empty() {
                        let mut gc = crate::sources::google::GoogleCalendar::new(email, safe_dir);
                        if gc.get_access_token().is_some() {
                            if let Some(ref ext) = evt.external_id {
                                graph_ok = Some(gc.respond_to_event(cal_id, ext, email, response));
                            } else {
                                graph_ok = Some(false);
                            }
                        } else {
                            graph_ok = Some(false);
                        }
                    }
                }
            }
        }

        let data = EventData {
            id: Some(evt.id),
            calendar_id: evt.calendar_id,
            external_id: evt.external_id.clone(),
            title: evt.title.clone(),
            description: evt.description.clone(),
            location: evt.location.clone(),
            start_time: evt.start_time,
            end_time: evt.end_time,
            all_day: evt.all_day,
            timezone: evt.timezone.clone(),
            recurrence_rule: evt.recurrence_rule.clone(),
            series_master_id: evt.series_master_id,
            status: evt.status.clone(),
            organizer: evt.organizer.clone(),
            attendees: evt.attendees.clone(),
            my_status: Some(my_status_value.to_string()),
            alarms: evt.alarms.clone(),
            metadata: evt.metadata.clone(),
        };
        let _ = self.db.save_event(&data);
        self.load_events_for_range();
        self.render_all();

        let msg = match graph_ok {
            Some(true)  => format!("{} (organizer notified)", humanize_status(my_status_value)),
            Some(false) => format!("{} locally — RSVP propagation failed", humanize_status(my_status_value)),
            None        => format!("{} locally — no propagation for this calendar", humanize_status(my_status_value)),
        };
        let color = if matches!(graph_ok, Some(false)) { 196 } else { 156 };
        self.show_feedback(&msg, color);
    }

    /// Free/busy overlay: prompt for comma-separated emails, call Microsoft
    /// Graph getSchedule against the first configured Outlook calendar, and
    /// render a compact grid in the bottom pane. One row per person, one
    /// column per 30-min slot from 08:00 to 18:00 on the currently selected
    /// day (so 20 cells per person). Cell legend: · free, ~ tentative,
    /// █ busy, ◎ OOF, e elsewhere.
    fn show_free_busy(&mut self) {
        let emails_raw = self.bottom_ask(" Emails (comma-separated): ", "");
        let emails_raw = emails_raw.trim().to_string();
        if emails_raw.is_empty() {
            self.render_all();
            return;
        }
        let emails: Vec<String> = emails_raw
            .split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty()).collect();
        if emails.is_empty() {
            self.show_feedback("No emails provided", 245);
            return;
        }

        // First Outlook calendar (getSchedule is a per-user API; any auth works).
        let oc_config = match self.db.get_calendars(false).ok().and_then(|cals| {
            cals.into_iter()
                .find(|c| c.source_type == "outlook")
                .and_then(|c| c.source_config)
        }) {
            Some(cfg) => cfg,
            None => { self.show_feedback("No Outlook calendar configured (need it for getSchedule)", 196); return; }
        };
        let config: serde_json::Value = match serde_json::from_str(&oc_config) {
            Ok(v) => v,
            Err(e) => { self.show_feedback(&format!("Bad Outlook config: {}", e), 196); return; }
        };
        let mut oc = crate::sources::outlook::OutlookCalendar::new(&config);
        if oc.refresh_access_token().is_none() {
            self.show_feedback(&format!("Graph auth failed: {}",
                oc.last_error.as_deref().unwrap_or("unknown")), 196);
            return;
        }

        // Window: 08:00 to 18:00 local on the selected day, 30-min slots.
        let (sy, sm, sd) = self.selected_date;
        let start = format!("{:04}-{:02}-{:02}T08:00:00", sy, sm, sd);
        let end   = format!("{:04}-{:02}-{:02}T18:00:00", sy, sm, sd);
        let tz = std::env::var("TZ").unwrap_or_else(|_| "Europe/Oslo".to_string());

        self.show_feedback(&format!("Fetching schedule for {} people...", emails.len()), 226);
        let schedules = match oc.get_schedule(&emails, &start, &end, &tz, 30) {
            Some(s) => s,
            None => { self.show_feedback(&format!("getSchedule failed: {}",
                oc.last_error.as_deref().unwrap_or("no response")), 196); return; }
        };

        // Render grid. 20 half-hour slots from 08:00 to 18:00.
        // Columns: time header (08:00 marker every 2 slots).
        let mut lines: Vec<String> = Vec::new();
        lines.push(style::bold(&format!(
            " Availability for {:04}-{:02}-{:02}  08:00-18:00  (30-min slots)",
            sy, sm, sd)));
        lines.push(String::new());
        // Hour-tick header.
        let mut header = String::from(format!(" {:>28}  ", ""));
        for slot in 0..20 {
            if slot % 2 == 0 {
                let hour = 8 + (slot / 2);
                header.push_str(&format!("{:02}", hour));
            } else {
                header.push_str("  ");
            }
        }
        lines.push(style::fg(&header, 240));

        for entry in &schedules {
            let mut row = format!(" {:>28}  ", truncate_str(&entry.email, 28));
            for ch in entry.availability_view.chars() {
                let glyph = match ch {
                    '0' => style::fg("·", 108),  // free (muted green)
                    '1' => style::fg("~", 220),  // tentative
                    '2' => style::fg("\u{2588}", 167), // busy (red block)
                    '3' => style::fg("\u{25CE}", 208), // OOF
                    '4' => style::fg("e", 117),        // working elsewhere
                    _   => "?".to_string(),
                };
                // Display a single column per slot + padding inside header.
                row.push_str(&glyph);
                row.push(' ');
            }
            lines.push(row);
        }
        lines.push(String::new());
        lines.push(style::fg(
            "  ·=free  ~=tentative  █=busy  ◎=OOF  e=elsewhere    (F again to refresh, any key to dismiss)",
            240));

        self.bottom.say(&lines.join("\n"));
        let _ = crust::Input::getchr(None);
        self.render_all();
    }

    /// `J` (Join) — open the selected event's meeting URL.
    ///
    /// Launcher selection is config-driven via `meeting_handlers:` in
    /// `~/.tock/config.yml`. Each entry maps a host suffix to a
    /// command, e.g.
    ///
    /// ```yaml
    /// meeting_handlers:
    ///   teams.microsoft.com: teams-for-linux
    ///   zoom.us: ""             # empty = force xdg-open
    /// ```
    ///
    /// Host matching is suffix-based (so `us02web.zoom.us` matches a
    /// `zoom.us` entry). Empty values, missing entries, and missing
    /// binaries all fall back to `xdg-open` — which hands the URL to
    /// the user's default browser. Detached spawn so tock stays in
    /// the foreground.
    fn join_meeting(&mut self) {
        let evt = match self.event_at_selected_slot() {
            Some(e) => e,
            None => { self.show_feedback("No event at this time slot", 245); return; }
        };
        let haystack = {
            let desc = evt.description.as_deref().unwrap_or("");
            let loc  = evt.location.as_deref().unwrap_or("");
            format!("{}\n{}", desc, loc)
        };
        let Some(url) = extract_meeting_url(&haystack) else {
            self.show_feedback(
                "No meeting URL found in description or location", 245);
            return;
        };

        // Walk meeting_handlers from longest suffix to shortest so
        // `teams.microsoft.com` wins over a hypothetical bare
        // `microsoft.com` entry.
        let host = url_host(&url).unwrap_or_default();
        let handlers = self.config.get(
            "meeting_handlers",
            serde_yaml::Value::Mapping(Default::default()),
        );
        let mut configured: Option<String> = None;
        if let serde_yaml::Value::Mapping(m) = handlers {
            let mut entries: Vec<(String, String)> = m.into_iter()
                .filter_map(|(k, v)| {
                    let key = k.as_str()?.to_string();
                    let val = v.as_str().unwrap_or("").to_string();
                    Some((key, val))
                })
                .collect();
            entries.sort_by_key(|(k, _)| std::cmp::Reverse(k.len()));
            for (suffix, cmd) in entries {
                if host == suffix || host.ends_with(&format!(".{}", suffix)) {
                    if !cmd.trim().is_empty() {
                        configured = Some(cmd);
                    }
                    break;
                }
            }
        }

        // Resolve the launcher. If the config says use `foo` but `foo`
        // isn't on PATH, drop down to xdg-open with a status note so
        // the user knows what happened.
        let (launcher, fallback) = match configured {
            Some(cmd) if which_on_path(&cmd) => (cmd, false),
            Some(cmd) => {
                self.show_feedback(
                    &format!("{} not in PATH, opening in browser…", cmd), 245);
                ("xdg-open".to_string(), true)
            }
            None => ("xdg-open".to_string(), false),
        };

        let spawned = std::process::Command::new(&launcher)
            .arg(&url)
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .spawn();
        match spawned {
            Ok(_) if !fallback => self.show_feedback(
                &format!("Joining via {}…", launcher), 156),
            Ok(_) => {}  // already showed the fallback note above
            Err(e) => self.show_feedback(
                &format!("Couldn't launch {}: {}", launcher, e), 196),
        }
    }

    /// `N` (Note) — open an Obsidian meeting note for the selected event.
    ///
    /// Shells out to `obsidian-note-open <event_id>`, which is responsible
    /// for: querying tock.db, generating a deterministic filename, creating
    /// the markdown from a template if absent, and launching the file via
    /// `open obsidian://…`. Detached spawn so tock stays in the foreground.
    fn open_meeting_note(&mut self) {
        let evt = match self.event_at_selected_slot() {
            Some(e) => e,
            None => { self.show_feedback("No event at this time slot", 245); return; }
        };
        let spawned = std::process::Command::new("obsidian-note-open")
            .arg(evt.id.to_string())
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .spawn();
        match spawned {
            Ok(_) => self.show_feedback(&format!("Opening note: {}", evt.title), 156),
            Err(e) => self.show_feedback(
                &format!("obsidian-note-open failed: {}", e), 196),
        }
    }

    /// `p` (Presentation) — open a Slidev deck for the selected event.
    ///
    /// Counterpart to `N` (note). Shells out to `tock-open-deck <event_id>`,
    /// which reads the event description, finds a `Slides-Slidev/decks/<slug>`
    /// path (or an http URL), and either launches the slidev dev server +
    /// browser or opens the URL. Detached spawn so tock stays foreground.
    fn open_presentation(&mut self) {
        let evt = match self.event_at_selected_slot() {
            Some(e) => e,
            None => { self.show_feedback("No event at this time slot", 245); return; }
        };
        let spawned = std::process::Command::new("tock-open-deck")
            .arg(evt.id.to_string())
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .spawn();
        match spawned {
            Ok(_) => self.show_feedback(&format!("Opening deck: {}", evt.title), 156),
            Err(e) => self.show_feedback(
                &format!("tock-open-deck failed: {}", e), 196),
        }
    }

    fn reply_via_kastrup(&mut self) {
        let evt = match self.event_at_selected_slot() {
            Some(e) => e,
            None => { self.show_feedback("No event at this time slot", 245); return; }
        };
        let organizer = evt.organizer.as_deref().unwrap_or("");
        if organizer.is_empty() {
            self.show_feedback("No organizer to reply to", 245);
            return;
        }
        // Launch kastrup with compose-to argument
        Crust::cleanup();
        let _ = std::process::Command::new("kastrup")
            .arg("--compose-to")
            .arg(organizer)
            .arg("--subject")
            .arg(&format!("Re: {}", evt.title))
            .status();
        Crust::init();
        Crust::set_app_identity("Tock");
        Crust::clear_screen();
        self.recreate_panes();
        self.render_all();
    }

    fn import_ics_file(&mut self) {
        self.blank_bottom(&style::bold(" Import ICS File"));
        let path = self.bottom_ask(" File path: ", "");
        if path.trim().is_empty() { self.render_all(); return; }

        let expanded = shellexpand(&path.trim());
        let p = Path::new(&expanded);
        if !p.exists() {
            self.show_feedback(&format!("File not found: {}", expanded), 196);
            return;
        }

        let cal_id = self.config.get_i64("default_calendar", 1);
        let result = ics::import_file(p, &self.db, cal_id);
        self.load_events_for_range();
        self.render_all();
        let mut msg = format!("Imported {} event(s)", result.imported);
        if result.skipped > 0 { msg.push_str(&format!(", skipped {}", result.skipped)); }
        let color = if result.error.is_some() { 196u8 } else { 156u8 };
        if let Some(ref err) = result.error { msg.push_str(&format!(" ({})", err)); }
        self.show_feedback(&msg, color);
    }

    fn setup_google_calendar(&mut self) {
        self.blank_bottom(&style::bold(&style::fg(" Google Calendar Setup", 39)));
        let email = self.bottom_ask(" Google email: ", "");
        if email.trim().is_empty() { self.render_all(); return; }
        let email = email.trim().to_string();

        let safe_dir = self.config.get_str("google.safe_dir", "~/.config/tock/credentials");
        self.show_feedback("Connecting to Google Calendar...", 226);

        let _google = sources::google::GoogleCalendar::new(&email, Some(&safe_dir));
        // Google calendar setup is complex; show instructions
        self.show_feedback("Google Calendar: see credentials setup documentation", 245);
    }

    fn setup_outlook_calendar(&mut self) {
        self.blank_bottom(&style::bold(&style::fg(" Outlook/365 Calendar Setup", 33)));
        let default_client_id = self.config.get_str("outlook.client_id", "");
        let client_id = self.bottom_ask(" Azure App client_id: ", &default_client_id);
        if client_id.trim().is_empty() { self.render_all(); return; }

        let default_tenant = self.config.get_str("outlook.tenant_id", "common");
        let tenant_id = self.bottom_ask(
            &format!(" Tenant ID (Enter for '{}'): ", default_tenant), &default_tenant);
        let tenant_id = if tenant_id.trim().is_empty() { default_tenant } else { tenant_id.trim().to_string() };

        self.config.set("outlook.client_id", serde_yaml::Value::String(client_id.trim().to_string()));
        self.config.set("outlook.tenant_id", serde_yaml::Value::String(tenant_id.clone()));
        let _ = self.config.save();

        self.show_feedback("Outlook Calendar: device code auth not yet integrated in Tock", 245);
    }

    fn manual_sync(&mut self) {
        let google_cals: Vec<_> = self.db.get_calendars(true).unwrap_or_default()
            .into_iter().filter(|c| c.source_type == "google").collect();
        let outlook_cals: Vec<_> = self.db.get_calendars(true).unwrap_or_default()
            .into_iter().filter(|c| c.source_type == "outlook").collect();

        if google_cals.is_empty() && outlook_cals.is_empty() {
            self.show_feedback("No remote calendars configured. Press G (Google) or O (Outlook) to set up.", 245);
            return;
        }

        self.syncing = true;
        self.render_status_bar();
        self.show_feedback("Syncing...", 156);

        // Run sync directly on main thread for immediate feedback
        let now = crate::database::now_secs();
        let range_start = now - 90 * 86400;
        let range_end = now + 90 * 86400;
        let mut any_new = false;

        for cal in &google_cals {
            let cfg_str = match &cal.source_config { Some(s) => s.clone(), None => continue };
            let config: serde_json::Value = match serde_json::from_str(&cfg_str) {
                Ok(v) => v,
                Err(_) => continue,
            };
            let email = config.get("email").and_then(|v| v.as_str()).unwrap_or("");
            let safe_dir = config.get("safe_dir").and_then(|v| v.as_str());
            let gcid = config.get("google_calendar_id").and_then(|v| v.as_str()).unwrap_or("");
            let mut gc = crate::sources::google::GoogleCalendar::new(email, safe_dir);
            if gc.get_access_token().is_none() {
                let err = gc.last_error.as_deref().unwrap_or("auth failed");
                self.show_feedback(&format!("Google sync {}: {}", cal.name, err), 196);
                continue;
            }
            let tmin = crate::sources::google::ts_to_rfc3339_pub(range_start);
            let tmax = crate::sources::google::ts_to_rfc3339_pub(range_end);
            if let Some(events) = gc.fetch_events(gcid, &tmin, &tmax) {
                for mut ev in events {
                    ev.calendar_id = cal.id;
                    if let Ok(crate::database::SyncResult::New | crate::database::SyncResult::Updated) =
                        self.db.upsert_synced_event(cal.id, &ev)
                    {
                        any_new = true;
                    }
                }
                let _ = self.db.update_calendar_sync(cal.id, now, None);
            }
        }

        for cal in &outlook_cals {
            let cfg_str = match &cal.source_config { Some(s) => s.clone(), None => continue };
            let mut config: serde_json::Value = match serde_json::from_str(&cfg_str) {
                Ok(v) => v,
                Err(_) => continue,
            };
            let mut oc = crate::sources::outlook::OutlookCalendar::new(&config);
            if oc.refresh_access_token().is_none() {
                let err = oc.last_error.as_deref().unwrap_or("auth failed");
                self.show_feedback(&format!("Outlook sync {}: {}", cal.name, err), 196);
                continue;
            }
            let tmin = crate::sources::google::ts_to_rfc3339_pub(range_start);
            let tmax = crate::sources::google::ts_to_rfc3339_pub(range_end);
            if let Some(events) = oc.fetch_events(&tmin, &tmax) {
                for mut ev in events {
                    ev.calendar_id = cal.id;
                    if let Ok(crate::database::SyncResult::New | crate::database::SyncResult::Updated) =
                        self.db.upsert_synced_event(cal.id, &ev)
                    {
                        any_new = true;
                    }
                }
                let new_cfg = if let Some(rt) = oc.get_refresh_token() {
                    config["refresh_token"] = serde_json::json!(rt);
                    if let Some(at) = oc.get_access_token_cached() {
                        config["access_token"] = serde_json::json!(at);
                    }
                    Some(serde_json::to_string(&config).unwrap_or_default())
                } else { None };
                let _ = self.db.update_calendar_sync(cal.id, now, new_cfg.as_deref());
            }
        }

        self.syncing = false;
        if any_new {
            self.load_events_for_range();
            self.render_all();
            self.show_feedback("Sync complete, new events loaded", 156);
        } else {
            self.render_status_bar();
            self.show_feedback("Sync complete, no changes", 245);
        }
    }

    fn show_calendars(&mut self) {
        let mut calendars = self.db.get_calendars(false).unwrap_or_default();
        if calendars.is_empty() {
            self.show_feedback("No calendars configured", 245);
            return;
        }

        let pw = (self.cols.saturating_sub(16) as usize).min(64).max(50) as u16;
        let ph = (calendars.len() as u16 + 7).min(self.rows.saturating_sub(6));
        let px = (self.cols.saturating_sub(pw)) / 2;
        let py = (self.rows.saturating_sub(ph)) / 2;

        let mut popup = Pane::new(px, py, pw, ph, 252, 0);
        popup.border = true;
        popup.scroll = false;

        let mut sel = 0usize;

        let build = |calendars: &[database::Calendar], sel: usize, popup: &mut Pane, pw: u16| {
            popup.full_refresh();
            let mut lines = Vec::new();
            lines.push(String::new());
            lines.push(format!("  {}", style::bold("Calendars")));
            let sep_w = (pw as usize).saturating_sub(6).max(1);
            lines.push(format!("  {}", style::fg(&"-".repeat(sep_w), 238)));

            for (i, cal) in calendars.iter().enumerate() {
                let color = cal.color as u8;
                let swatch = style::fg("\u{2588}\u{2588}", color);
                let status = if cal.enabled {
                    style::fg("on", 35)
                } else {
                    style::fg("off", 196)
                };
                let src = &cal.source_type;
                let name = &cal.name;
                let name_trunc = truncate_str(name, 22);
                let display = format!("  {} {:<22} {}  [{}]", swatch, name_trunc, status, src);
                if i == sel {
                    lines.push(style::bold(&style::fg(&display, 39)));
                } else {
                    lines.push(display);
                }
            }

            lines.push(String::new());
            lines.push(format!("  {}", style::fg("j/k:nav  o:only  a:all  c:color  ENTER:toggle  x:remove  q:close", 245)));
            popup.set_text(&lines.join("\n"));
            popup.ix = 0;
            popup.refresh();
        };

        build(&calendars, sel, &mut popup, pw);

        loop {
            let k = Input::getchr(None);
            match k.as_deref() {
                Some("ESC") | Some("q") => break,
                Some("k") | Some("UP") => {
                    sel = if sel == 0 { calendars.len() - 1 } else { sel - 1 };
                    build(&calendars, sel, &mut popup, pw);
                }
                Some("j") | Some("DOWN") => {
                    sel = (sel + 1) % calendars.len();
                    build(&calendars, sel, &mut popup, pw);
                }
                Some("c") => {
                    let cal = &calendars[sel];
                    if let Some(new_color) = self.pick_color(cal.color as u8) {
                        let _ = self.db.update_calendar_color(calendars[sel].id, new_color as i64);
                        calendars[sel].color = new_color as i64;
                    }
                    // Recreate popup after color picker
                    popup = Pane::new(px, py, pw, ph, 252, 0);
                    popup.border = true;
                    popup.scroll = false;
                    build(&calendars, sel, &mut popup, pw);
                }
                Some("ENTER") => {
                    let _ = self.db.toggle_calendar_enabled(calendars[sel].id);
                    calendars[sel].enabled = !calendars[sel].enabled;
                    build(&calendars, sel, &mut popup, pw);
                }
                Some("x") => {
                    let name = calendars[sel].name.clone();
                    let confirm = popup.ask(&format!(" Remove '{}'? (y/n): ", name), "");
                    if confirm.trim().to_lowercase() == "y" {
                        let _ = self.db.delete_calendar_with_events(calendars[sel].id);
                        calendars.remove(sel);
                        if calendars.is_empty() { break; }
                        if sel >= calendars.len() { sel = calendars.len() - 1; }
                    }
                    build(&calendars, sel, &mut popup, pw);
                }
                Some("o") => {
                    // Solo: enable only the selected calendar. If it's already
                    // the sole enabled one, restore all to enabled (un-solo).
                    let enabled_count = calendars.iter().filter(|c| c.enabled).count();
                    let already_solo = enabled_count == 1 && calendars[sel].enabled;
                    if already_solo {
                        for cal in calendars.iter_mut() {
                            if !cal.enabled {
                                let _ = self.db.toggle_calendar_enabled(cal.id);
                                cal.enabled = true;
                            }
                        }
                    } else {
                        for (i, cal) in calendars.iter_mut().enumerate() {
                            let want = i == sel;
                            if cal.enabled != want {
                                let _ = self.db.toggle_calendar_enabled(cal.id);
                                cal.enabled = want;
                            }
                        }
                    }
                    build(&calendars, sel, &mut popup, pw);
                }
                Some("a") => {
                    // Enable all calendars
                    for cal in calendars.iter_mut() {
                        if !cal.enabled {
                            let _ = self.db.toggle_calendar_enabled(cal.id);
                            cal.enabled = true;
                        }
                    }
                    build(&calendars, sel, &mut popup, pw);
                }
                _ => {}
            }
        }

        Crust::clear_screen();
        self.recreate_panes();
        self.load_events_for_range();
        self.render_all();
    }

    /// Resolved path of the quotes file (`quotes.file` in config.yml).
    fn quotes_path(&self) -> String {
        let path = self.config.get_str(
            "quotes.file",
            "~/Obsidian/Miles PKM/3 Areas/personal/quotes.md",
        );
        if let Some(rest) = path.strip_prefix("~/") {
            format!("{}/{}", std::env::var("HOME").unwrap_or_default(), rest)
        } else {
            path
        }
    }

    /// `"` — recall-practice the current wall quote: the popup shows the 中文
    /// as the prompt (plus author + first-word/word-count hint), the English
    /// stays hidden — type it from memory, ENTER reveals it with a char-level
    /// diff. The wall quote is hidden while the popup is open so the answer
    /// isn't sitting on the backdrop. Attempts are logged to
    /// ~/.tock/quote_practice.log; perfect runs feed the wall's ·N counter.
    fn practice_quote(&mut self) {
        let quotes = load_quotes(&self.quotes_path());
        if quotes.is_empty() {
            self.show_feedback("quotes.md 沒有句子（要 `- ` 開頭的行）", 245);
            return;
        }
        let q = &quotes[quote_index(quotes.len())];
        let (body, author) = split_author(&q.en);
        let target: Vec<char> = body.trim().chars().collect();

        // Hide the answer on the backdrop while practicing.
        self.hide_wall_quote = true;
        self.render_top_pane();

        let pw = (self.cols.saturating_sub(8)).min(90).max(60);
        let ph = self.rows.saturating_sub(6).min(20);
        let px = (self.cols.saturating_sub(pw)) / 2;
        let py = (self.rows.saturating_sub(ph)) / 2;
        let mut popup = Pane::new(px, py, pw, ph, 252, 0);
        popup.border = true;
        popup.scroll = false;

        let wrap_w = (pw as usize).saturating_sub(8).max(20);

        // Per-char styled render with manual CJK-safe wrapping: good chars in
        // ok_fg, bad chars (wrong/extra/missed) underlined in bad_fg.
        let render_marked = |chars: &[char], good: &[bool], ok_fg: u8, bad_fg: u8| -> Vec<String> {
            let mut lines = Vec::new();
            let mut cur = String::new();
            let mut w = 0usize;
            for (i, &c) in chars.iter().enumerate() {
                let cw = display_width(&c.to_string());
                if w + cw > wrap_w {
                    lines.push(std::mem::take(&mut cur));
                    w = 0;
                }
                let s = c.to_string();
                if good[i] {
                    cur.push_str(&style::fg(&s, ok_fg));
                } else {
                    cur.push_str(&style::underline(&style::fg(&s, bad_fg)));
                }
                w += cw;
            }
            if !cur.is_empty() || lines.is_empty() {
                lines.push(cur);
            }
            lines
        };

        // (errors, target_hit, typed_chars, typed_ok)
        let mut result: Option<(usize, Vec<bool>, Vec<char>, Vec<bool>)> = None;
        let mut typed = String::new();

        loop {
            // ----- render -----
            let mut lines = Vec::new();
            lines.push(String::new());
            lines.push(format!("  {}", style::fg("❝ Practice", 117)));
            lines.push(String::new());
            // Recall mode: the 中文 is the prompt; the English stays hidden
            // until the answer is revealed. Hint = first word + word count.
            // No 中文 on a quote → nothing to recall from, show the English.
            match (&q.zh, &result) {
                (Some(zh), None) => {
                    for l in wrap_display(zh, wrap_w) {
                        lines.push(format!("   {}", style::fg(&l, 250)));
                    }
                    if let Some(a) = author {
                        lines.push(format!("   {}", style::fg(&format!("— {}", a), 242)));
                    }
                    let n_words = body.split_whitespace().count();
                    if let Some(first) = body.split_whitespace().next() {
                        lines.push(format!(
                            "   {}",
                            style::fg(&format!("{} …（{} words）", first, n_words), 245)
                        ));
                    }
                }
                _ => {
                    for l in wrap_display(body, wrap_w) {
                        lines.push(format!("   {}", style::fg(&l, 250)));
                    }
                    if let Some(a) = author {
                        lines.push(format!("   {}", style::fg(&format!("— {}", a), 242)));
                    }
                    if let Some(ref zh) = q.zh {
                        for l in wrap_display(zh, wrap_w) {
                            lines.push(format!("   {}", style::fg(&l, 245)));
                        }
                    }
                }
            }
            let sep_w = (pw as usize).saturating_sub(6).max(1);
            lines.push(format!("  {}", style::fg(&"-".repeat(sep_w), 238)));

            match &result {
                None => {
                    let all_good = vec![true; typed.chars().count()];
                    let tchars: Vec<char> = typed.chars().collect();
                    let mut tlines = render_marked(&tchars, &all_good, 252, 252);
                    if let Some(last) = tlines.last_mut() {
                        last.push_str(&style::fg("▏", 51));
                    }
                    for (i, l) in tlines.iter().enumerate() {
                        let prompt = if i == 0 { "> " } else { "  " };
                        lines.push(format!("  {}{}", style::fg(prompt, 51), l));
                    }
                    lines.push(String::new());
                    lines.push(format!("  {}", style::fg("ENTER:對答案  ESC:離開", 245)));
                }
                Some((errors, hit, tchars, ok)) => {
                    for (i, l) in render_marked(tchars, ok, 252, 203).iter().enumerate() {
                        let tag = if i == 0 { "你打的 " } else { "       " };
                        lines.push(format!("  {}{}", style::fg(tag, 245), l));
                    }
                    for (i, l) in render_marked(&target, hit, 245, 220).iter().enumerate() {
                        let tag = if i == 0 { "原句   " } else { "       " };
                        lines.push(format!("  {}{}", style::fg(tag, 245), l));
                    }
                    lines.push(String::new());
                    if *errors == 0 {
                        lines.push(format!("  {}", style::fg("✓ 全對！已記一次", 156)));
                    } else {
                        lines.push(format!(
                            "  {}",
                            style::fg(&format!("✗ {} 處差異（底線標出）", errors), 203)
                        ));
                    }
                    lines.push(String::new());
                    lines.push(format!("  {}", style::fg("r:再打一次  ENTER/ESC:關閉", 245)));
                }
            }

            while lines.len() < (ph as usize).saturating_sub(2) {
                lines.push(String::new());
            }
            popup.full_refresh();
            popup.set_text(&lines.join("\n"));
            popup.ix = 0;
            popup.refresh();

            // ----- input -----
            let k = Input::getchr(None);
            match k.as_deref() {
                Some("ESC") | Some("RESIZE") => break,
                Some("ENTER") => {
                    if result.is_some() {
                        break;
                    }
                    let tchars: Vec<char> = typed.trim().chars().collect();
                    let (hit, ok) = char_diff(&target, &tchars);
                    let errors = hit.iter().filter(|h| !**h).count()
                        + ok.iter().filter(|o| !**o).count();
                    append_practice_log(&q.en, errors);
                    result = Some((errors, hit, tchars, ok));
                }
                Some("BACK") => {
                    if result.is_none() {
                        typed.pop();
                    }
                }
                Some("r") if result.is_some() => {
                    typed.clear();
                    result = None;
                }
                Some(s) => {
                    if result.is_none() {
                        let cs: Vec<char> = s.chars().collect();
                        if cs.len() == 1 && !cs[0].is_control() {
                            typed.push(cs[0]);
                        }
                    }
                }
                None => {}
            }
        }

        self.hide_wall_quote = false;
        Crust::clear_screen();
        self.recreate_panes();
        self.render_all();
    }

    /// Spotlight-style live keyword search across events in ±2 year window.
    /// `/` opens, type to narrow, ↑↓ pick, ENTER jumps to event's date, ESC cancels.
    fn search_events(&mut self) {
        let now = database::now_secs();
        let two_years: i64 = 2 * 365 * 24 * 3600;
        let events = match self.db.get_events_in_range(now - two_years, now + two_years) {
            Ok(v) => v,
            Err(_) => { self.show_feedback("Search failed", 196); return; }
        };
        if events.is_empty() {
            self.show_feedback("No events in ±2 year window", 245);
            return;
        }

        // Sort by distance from now (most relevant first).
        let mut by_relevance: Vec<usize> = (0..events.len()).collect();
        by_relevance.sort_by_key(|&i| (events[i].start_time - now).abs());

        let pw = (self.cols.saturating_sub(8) as usize).min(90).max(60) as u16;
        let ph = self.rows.saturating_sub(4).min(28);
        let px = (self.cols.saturating_sub(pw)) / 2;
        let py = (self.rows.saturating_sub(ph)) / 2;

        let mut popup = Pane::new(px, py, pw, ph, 252, 0);
        popup.border = true;
        popup.scroll = false;

        let mut query = String::new();
        let mut sel = 0usize;
        let tz = local_tz_offset_secs();

        let filter = |q: &str, events: &[Event], by_relevance: &[usize]| -> Vec<usize> {
            if q.is_empty() {
                return by_relevance.iter().copied().collect();
            }
            let ql = q.to_lowercase();
            by_relevance.iter().copied().filter(|&i| {
                let e = &events[i];
                if e.title.to_lowercase().contains(&ql) { return true; }
                if let Some(ref l) = e.location {
                    if l.to_lowercase().contains(&ql) { return true; }
                }
                if let Some(ref d) = e.description {
                    if d.to_lowercase().contains(&ql) { return true; }
                }
                false
            }).collect()
        };

        let render = |popup: &mut Pane, query: &str, results: &[usize], events: &[Event], sel: usize, pw: u16, ph: u16, tz: i64| {
            popup.full_refresh();
            let mut lines = Vec::new();
            lines.push(String::new());
            lines.push(format!("  / {}{}", query, style::fg("_", 51)));
            let sep_w = (pw as usize).saturating_sub(6).max(1);
            lines.push(format!("  {}", style::fg(&"-".repeat(sep_w), 238)));

            let max_results = (ph as usize).saturating_sub(7);

            if results.is_empty() {
                lines.push(format!("  {}", style::fg("(no matches)", 245)));
            } else {
                for (idx, &ei) in results.iter().take(max_results).enumerate() {
                    let e = &events[ei];
                    let local_s = e.start_time + tz;
                    let (y, m, d, sh, smn, _) = ts_to_parts(local_s);
                    let when = if e.all_day {
                        format!("{:04}-{:02}-{:02}      ", y, m, d)
                    } else {
                        format!("{:04}-{:02}-{:02} {:02}:{:02}", y, m, d, sh, smn)
                    };
                    let title = if e.title.is_empty() { "(no title)".to_string() } else { e.title.clone() };
                    let title_trunc = truncate_str(&title, (pw as usize).saturating_sub(28));
                    let color = e.calendar_color as u8;
                    let swatch = style::fg("\u{2588}", color);
                    // Selection visual: layered cues so it survives CJK (no bold
                    // glyph) and varied terminals — bright marker + brighter
                    // date + underline (terminal mode, not font weight).
                    if idx == sel {
                        let marker = style::fg(">", 51);
                        let when_s = style::fg(&when, 252);
                        let body = format!("{} {} {}  {}", marker, swatch, when_s, title_trunc);
                        lines.push(format!("  {}", style::underline(&body)));
                    } else {
                        let when_s = style::fg(&when, 245);
                        let body = format!("  {} {}  {}", swatch, when_s, title_trunc);
                        lines.push(format!("  {}", body));
                    }
                }
                if results.len() > max_results {
                    lines.push(format!("  {}", style::fg(&format!("... +{} more (type to narrow)", results.len() - max_results), 245)));
                }
            }

            while lines.len() < (ph as usize).saturating_sub(2) { lines.push(String::new()); }
            let footer = format!("{} match{}  ·  UP/DOWN:nav  ENTER:jump  ESC:cancel",
                results.len(), if results.len() == 1 { "" } else { "es" });
            lines.push(format!("  {}", style::fg(&footer, 245)));
            popup.set_text(&lines.join("\n"));
            popup.ix = 0;
            popup.refresh();
        };

        let mut results = filter(&query, &events, &by_relevance);
        render(&mut popup, &query, &results, &events, sel, pw, ph, tz);

        let mut jump_to: Option<usize> = None;

        loop {
            let k = Input::getchr(None);
            match k.as_deref() {
                Some("ESC") => break,
                Some("RESIZE") => break,
                Some("ENTER") => {
                    if !results.is_empty() && sel < results.len() {
                        jump_to = Some(results[sel]);
                    }
                    break;
                }
                Some("UP") => {
                    if !results.is_empty() {
                        let visible = results.len().min((ph as usize).saturating_sub(7));
                        sel = if sel == 0 { visible - 1 } else { sel - 1 };
                        render(&mut popup, &query, &results, &events, sel, pw, ph, tz);
                    }
                }
                Some("DOWN") => {
                    if !results.is_empty() {
                        let visible = results.len().min((ph as usize).saturating_sub(7));
                        sel = (sel + 1) % visible;
                        render(&mut popup, &query, &results, &events, sel, pw, ph, tz);
                    }
                }
                Some("BACK") => {
                    if query.pop().is_some() {
                        results = filter(&query, &events, &by_relevance);
                        sel = 0;
                        render(&mut popup, &query, &results, &events, sel, pw, ph, tz);
                    }
                }
                Some(s) => {
                    let chars: Vec<char> = s.chars().collect();
                    if chars.len() == 1 && !chars[0].is_control() {
                        query.push(chars[0]);
                        results = filter(&query, &events, &by_relevance);
                        sel = 0;
                        render(&mut popup, &query, &results, &events, sel, pw, ph, tz);
                    }
                }
                None => {}
            }
        }

        Crust::clear_screen();
        self.recreate_panes();

        if let Some(ei) = jump_to {
            let e = &events[ei];
            let local_s = e.start_time + tz;
            let (y, m, d, sh, smn, _) = ts_to_parts(local_s);
            self.selected_date = (y, m, d);
            // Snap cursor to event's slot AND scroll grid so it's actually
            // visible. Without this, jumping to a 10:00 event while user was
            // looking at the afternoon kept slot_offset stale → event sits
            // above the visible window and looks like nothing happened.
            if e.all_day {
                self.selected_slot = -1;
            } else {
                let slot = (sh * 2 + if smn >= 30 { 1 } else { 0 }) as i32;
                self.selected_slot = slot;
                self.slot_offset = (slot - 5).max(0);
            }
            self.date_changed();
        } else {
            self.load_events_for_range();
        }
        self.render_all();
    }

    fn pick_color(&mut self, current: u8) -> Option<u8> {
        let pw = 52u16;
        let ph = 20u16;
        let px = (self.cols.saturating_sub(pw)) / 2;
        let py = (self.rows.saturating_sub(ph)) / 2;

        let mut popup = Pane::new(px, py, pw, ph, 252, 0);
        popup.border = true;
        popup.scroll = false;

        let mut sel = current as u16;

        let build = |sel: u16, popup: &mut Pane| {
            popup.full_refresh();
            let mut lines = Vec::new();
            lines.push(String::new());
            lines.push(format!("  {}  current: {} {}",
                style::bold("Pick Color"),
                style::fg("\u{2588}\u{2588}", sel as u8),
                sel));
            lines.push(String::new());

            for row in 0..16u16 {
                let mut line = " ".to_string();
                for col in 0..16u16 {
                    let c = row * 16 + col;
                    if c == sel {
                        line.push_str(&style::bold(&style::fg(&style::bg("X ", c as u8), 255)));
                    } else {
                        line.push_str(&style::bg("  ", c as u8));
                    }
                    line.push(' ');
                }
                lines.push(line);
            }
            lines.push(String::new());
            lines.push(format!("  {}", style::fg("Arrows:move  ENTER:select  ESC:cancel", 245)));
            popup.set_text(&lines.join("\n"));
            popup.ix = 0;
            popup.refresh();
        };

        build(sel, &mut popup);

        let result;
        loop {
            let k = Input::getchr(None);
            match k.as_deref() {
                Some("ESC") | Some("q") => { result = None; break; }
                Some("ENTER") => { result = Some(sel as u8); break; }
                Some("RIGHT") | Some("l") => { sel = (sel + 1) % 256; build(sel, &mut popup); }
                Some("LEFT") | Some("h") => { sel = (sel + 255) % 256; build(sel, &mut popup); }
                Some("DOWN") | Some("j") => { sel = (sel + 16) % 256; build(sel, &mut popup); }
                Some("UP") | Some("k") => { sel = (sel + 240) % 256; build(sel, &mut popup); }
                _ => {}
            }
        }

        Crust::clear_screen();
        self.recreate_panes();
        self.render_all();
        result
    }

    fn show_preferences(&mut self) {
        let pw = (self.cols.saturating_sub(20) as usize).min(56).max(48) as u16;
        let ph = 19u16;
        let px = (self.cols.saturating_sub(pw)) / 2;
        let py = (self.rows.saturating_sub(ph)) / 2;

        let mut popup = Pane::new(px, py, pw, ph, 252, 0);
        popup.border = true;
        popup.scroll = false;

        let pref_keys: Vec<(&str, &str, i64)> = vec![
            ("colors.selected_bg_a",   "Sel. alt bg A",     235),
            ("colors.selected_bg_b",   "Sel. alt bg B",     234),
            ("colors.alt_bg_a",        "Row alt bg A",      233),
            ("colors.alt_bg_b",        "Row alt bg B",      0),
            ("colors.current_month_bg","Current month bg",  233),
            ("colors.saturday",        "Saturday color",    208),
            ("colors.sunday",          "Sunday color",      167),
            ("colors.today_fg",        "Today fg",          232),
            ("colors.today_bg",        "Today bg",          246),
            ("colors.slot_selected_bg","Slot selected bg",  237),
            ("colors.info_bg",         "Info bar bg",       235),
            ("colors.status_bg",       "Status bar bg",     235),
            ("work_hours.start",       "Work hours start",  8),
            ("work_hours.end",         "Work hours end",    17),
            ("default_calendar",       "Default calendar",  1),
        ];

        let mut sel = 0usize;

        let is_color = |key: &str| -> bool { key.starts_with("colors.") };

        let build = |sel: usize, popup: &mut Pane, config: &config::Config, db: &Database, pw: u16,
                     pref_keys: &[(&str, &str, i64)]| {
            popup.full_refresh();
            let inner_w = pw as usize - 4;
            let mut lines = Vec::new();
            lines.push(String::new());
            lines.push(format!("  {}", style::bold("Preferences")));
            lines.push(format!("  {}", style::fg(&"\u{2500}".repeat(inner_w.saturating_sub(3).max(1)), 238)));

            for (i, &(key, label, default)) in pref_keys.iter().enumerate() {
                let val = config.get_i64(key, default);
                let display = if key.starts_with("colors.") {
                    let swatch = if key.contains("bg") {
                        style::bg("  ", val as u8)
                    } else {
                        style::fg("\u{2588}\u{2588}", val as u8)
                    };
                    format!("  {:<18} {:>3} {}", label, val, swatch)
                } else if key == "default_calendar" {
                    let cal_name = db.get_calendars(false).ok()
                        .and_then(|cals| cals.iter().find(|c| c.id == val).map(|c| c.name.clone()))
                        .unwrap_or_default();
                    let extra = if cal_name.is_empty() { String::new() }
                        else { format!(" ({})", cal_name) };
                    format!("  {:<18} {}{}", label, val, extra)
                } else {
                    format!("  {:<18} {}", label, val)
                };

                if i == sel {
                    lines.push(style::bold(&style::fg(&display, 39)));
                } else {
                    lines.push(display);
                }
            }

            lines.push(String::new());
            let (key, _, _) = pref_keys[sel];
            if key.starts_with("colors.") {
                lines.push(format!("  {}", style::fg("j/k:navigate  h/l:adjust  H/L:x10  ENTER:type  q:close", 245)));
            } else {
                lines.push(format!("  {}", style::fg("j/k:navigate  ENTER:edit  q/ESC:close", 245)));
            }

            popup.set_text(&lines.join("\n"));
            popup.ix = 0;
            popup.refresh();
        };

        build(sel, &mut popup, &self.config, &self.db, pw, &pref_keys);

        loop {
            let k = Input::getchr(None);
            match k.as_deref() {
                Some("ESC") | Some("q") => break,
                Some("k") | Some("UP") => {
                    sel = if sel == 0 { pref_keys.len() - 1 } else { sel - 1 };
                    build(sel, &mut popup, &self.config, &self.db, pw, &pref_keys);
                }
                Some("j") | Some("DOWN") => {
                    sel = (sel + 1) % pref_keys.len();
                    build(sel, &mut popup, &self.config, &self.db, pw, &pref_keys);
                }
                Some("h") | Some("LEFT") | Some("l") | Some("RIGHT") | Some("H") | Some("L") => {
                    let (key, _, default) = pref_keys[sel];
                    if is_color(key) {
                        let delta: i64 = match k.as_deref() {
                            Some("h") | Some("LEFT") => -1,
                            Some("l") | Some("RIGHT") => 1,
                            Some("H") => -10,
                            Some("L") => 10,
                            _ => 0,
                        };
                        let val = (self.config.get_i64(key, default) + delta).clamp(0, 255);
                        self.config.set(key, serde_yaml::Value::Number(serde_yaml::Number::from(val)));
                        let _ = self.config.save();
                        build(sel, &mut popup, &self.config, &self.db, pw, &pref_keys);
                    }
                }
                Some("ENTER") => {
                    let (key, label, default) = pref_keys[sel];
                    if is_color(key) {
                        let current = self.config.get_i64(key, default);
                        if let Some(new_color) = self.pick_color(current as u8) {
                            self.config.set(key, serde_yaml::Value::Number(
                                serde_yaml::Number::from(new_color as i64)));
                            let _ = self.config.save();
                        }
                        popup = Pane::new(px, py, pw, ph, 252, 0);
                        popup.border = true;
                        popup.scroll = false;
                    } else {
                        let current = self.config.get_i64(key, default);
                        let result = popup.ask(&format!("{}: ", label), &current.to_string());
                        if !result.trim().is_empty() {
                            if let Ok(val) = result.trim().parse::<i64>() {
                                self.config.set(key, serde_yaml::Value::Number(
                                    serde_yaml::Number::from(val)));
                                let _ = self.config.save();
                            }
                        }
                    }
                    build(sel, &mut popup, &self.config, &self.db, pw, &pref_keys);
                }
                _ => {}
            }
        }

        Crust::clear_screen();
        self.recreate_panes();
        self.render_all();
    }

    fn show_help(&mut self) {
        let pw = (self.cols.saturating_sub(16) as usize).min(68).max(56) as u16;
        let ph = 24u16;
        let px = (self.cols.saturating_sub(pw)) / 2;
        let py = (self.rows.saturating_sub(ph)) / 2;

        let mut popup = Pane::new(px, py, pw, ph, 252, 0);
        popup.border = true;
        popup.scroll = false;

        let k = |s: &str| -> String { style::fg(s, 51) };
        let d = |s: &str| -> String { style::fg(s, 252) };
        let sep_w = (pw as usize).saturating_sub(6).max(1);
        let sep = format!("  {}", style::fg(&"-".repeat(sep_w), 238));

        let mut lines = Vec::new();
        lines.push(String::new());
        lines.push(format!("  {}", style::bold(&style::fg("Tock - Terminal Calendar", 156))));
        lines.push(sep.clone());
        lines.push(format!("  {}", style::bold(&style::fg("Navigation", 156))));
        lines.push(format!("  {}  {}        {}  {}", k("d/RIGHT"), d("Next day"), k("D/LEFT"), d("Prev day")));
        lines.push(format!("  {}        {}       {}       {}", k("w"), d("Next week"), k("W"), d("Prev week")));
        lines.push(format!("  {}        {}      {}       {}", k("m"), d("Next month"), k("M"), d("Prev month")));
        lines.push(format!("  {}        {}       {}       {}", k("y"), d("Next year"), k("Y"), d("Prev year")));
        lines.push(format!("  {}  {}", k("UP/DOWN"), d("Select time slot (scrolls at edges)")));
        lines.push(format!("  {}  {}   {}    {}", k("PgUp/Dn"), d("Jump 10 slots"), k("HOME"), d("Top/all-day")));
        lines.push(format!("  {}      {}  {}     {}", k("END"), d("Bottom (23:30)"), k("j/k"), d("Cycle events")));
        lines.push(format!("  {}      {}", k("e/E"), d("Jump to event (next/prev)")));
        lines.push(format!("  {}        {}           {}       {}", k("t"), d("Today"), k("g"), d("Go to (date, Mon, yyyy)")));
        lines.push(sep.clone());
        lines.push(format!("  {}", style::bold(&style::fg("Events", 156))));
        lines.push(format!("  {}        {}       {}   {}", k("n"), d("New event"), k("ENTER"), d("Edit event")));
        lines.push(format!("  {}    {}    {}       {}", k("x/DEL"), d("Delete event"), k("a"), d("Accept invite")));
        lines.push(format!("  {}        {}", k("v"), d("View event details (scrollable popup)")));
        lines.push(format!("  {}        {}", k("r"), d("Reply via Heathrow")));
        lines.push(format!("  {}        {}", k("J"), d("Join meeting (per-host handler from config, else browser)")));
        lines.push(format!("  {}        {}", k("p"), d("Open presentation (Slidev deck from event description)")));
        lines.push(sep.clone());
        lines.push(format!("  {}  {}   {}  {}   {}  {}", k("i"), d("Import ICS"), k("G"), d("Google setup"), k("O"), d("Outlook setup")));
        lines.push(format!("  {}  {}     {}  {}      {}  {}", k("S"), d("Sync now"), k("C"), d("Calendars"), k("P"), d("Preferences")));
        lines.push(format!("  {}        {}", k("\""), d("Practice the wall quote (type it, get a diff)")));
        lines.push(format!("  {}  {}", k("q"), d("Quit")));
        lines.push(String::new());
        lines.push(format!("  {}", style::fg("Press any key to close...", 245)));

        popup.set_text(&lines.join("\n"));
        popup.refresh();
        let _ = Input::getchr(None);
        Crust::clear_screen();
        self.recreate_panes();
        self.render_all();
    }

    // =====================================================================
    // Helper methods
    // =====================================================================

    fn show_feedback(&mut self, message: &str, color: u8) {
        let w = self.cols as usize;
        let mut lines = vec![
            style::fg(&"-".repeat(w), 238),
            style::fg(&format!(" {}", message), color),
        ];
        while lines.len() < self.bottom.h as usize {
            lines.push(String::new());
        }
        self.bottom.set_text(&lines.join("\n"));
        self.bottom.full_refresh();
    }

    fn blank_bottom(&mut self, header: &str) {
        let w = self.cols as usize;
        let mut lines = vec![style::fg(&"-".repeat(w), 238)];
        lines.push(String::new());
        if !header.is_empty() { lines.push(header.to_string()); }
        while lines.len() < self.bottom.h as usize {
            lines.push(String::new());
        }
        self.bottom.set_text(&lines.join("\n"));
        self.bottom.full_refresh();
    }

    fn bottom_ask(&mut self, prompt: &str, default: &str) -> String {
        let prompt_y = self.bottom.y + 3;
        let mut prompt_pane = Pane::new(1, prompt_y, self.cols, 1, 255, 0);
        prompt_pane.border = false;
        prompt_pane.scroll = false;
        prompt_pane.ask(prompt, default)
    }

    fn check_heathrow_goto(&mut self) {
        let goto_file = config::tock_home().join("goto");
        if !goto_file.exists() { return; }
        if let Ok(content) = std::fs::read_to_string(&goto_file) {
            let _ = std::fs::remove_file(&goto_file);
            let content = content.trim().to_string();
            if content.is_empty() { return; }
            if let Some(parsed) = self.parse_go_to_input(&content) {
                self.selected_date = parsed;
                self.selected_event_index = 0;
                self.load_events_for_range();
                self.render_all();
            }
        }
    }
}

// =========================================================================
// Free functions
// =========================================================================

fn add_days(date: (i32, u32, u32), n: i32) -> (i32, u32, u32) {
    let (y, m, d) = date;
    // Use noon to avoid DST boundary issues
    let ts = date_to_ts(y, m, d, 12, 0, 0) + (n as i64) * 86400;
    let (ny, nm, nd, _, _, _) = ts_to_parts(ts);
    (ny, nm, nd)
}

fn day_diff(a: (i32, u32, u32), b: (i32, u32, u32)) -> i64 {
    let ts_a = date_to_ts(a.0, a.1, a.2, 0, 0, 0);
    let ts_b = date_to_ts(b.0, b.1, b.2, 0, 0, 0);
    ((ts_a - ts_b) / 86400).abs()
}

fn truncate_str(s: &str, max: usize) -> String {
    if s.len() <= max { s.to_string() }
    else { s.chars().take(max).collect() }
}

/// Display width of a single char in terminal cells. East Asian wide /
/// fullwidth ranges count as 2, everything else as 1. Approximation but
/// covers the CJK / fullwidth ranges that matter for tock users.
fn char_display_width(c: char) -> usize {
    let cu = c as u32;
    if (0x1100..=0x115F).contains(&cu)
        || (0x2E80..=0x303E).contains(&cu)
        || (0x3041..=0x33FF).contains(&cu)
        || (0x3400..=0x4DBF).contains(&cu)
        || (0x4E00..=0x9FFF).contains(&cu)
        || (0xA000..=0xA4CF).contains(&cu)
        || (0xAC00..=0xD7A3).contains(&cu)
        || (0xF900..=0xFAFF).contains(&cu)
        || (0xFE30..=0xFE4F).contains(&cu)
        || (0xFF00..=0xFF60).contains(&cu)
        || (0xFFE0..=0xFFE6).contains(&cu)
        || (0x20000..=0x2FFFD).contains(&cu)
        || (0x30000..=0x3FFFD).contains(&cu)
    { 2 } else { 1 }
}

/// Slice `s` by terminal display width: skip `start_w` cells, then emit up
/// to `max_w` cells worth of characters. Used for wrapping long titles
/// across the rows that an event already occupies in the time grid.
fn slice_by_display(s: &str, start_w: usize, max_w: usize) -> String {
    let mut consumed = 0usize;
    let mut emitted = 0usize;
    let mut result = String::new();
    for c in s.chars() {
        let cw = char_display_width(c);
        if consumed >= start_w {
            if emitted + cw > max_w { break; }
            result.push(c);
            emitted += cw;
        }
        consumed += cw;
    }
    result
}

fn body_color(name: &str) -> String {
    for &(n, c) in orbit::BODY_COLORS {
        if n == name { return c.to_string(); }
    }
    "888888".to_string()
}

/// Two-letter Latin abbreviation for the planet name returned by
/// `orbit::visible_planets`. Used by the tock header so the planet
/// row renders uniformly across terminals — the astrological glyphs
/// from orbit don't all honour VS-15 on every font stack (Venus and
/// Mars in particular tend to upgrade to emoji), and a mixed row of
/// some-text some-emoji looks worse than this clean letter set.
fn planet_abbrev(name: &str) -> &'static str {
    match name {
        "Mercury" => "Me",
        "Venus"   => "Ve",
        "Mars"    => "Ma",
        "Jupiter" => "Ju",
        "Saturn"  => "Sa",
        "Uranus"  => "Ur",
        "Neptune" => "Ne",
        _ => "?",
    }
}

/// Subtle single-glyph RSVP marker: a dot for "accepted" / "organizer",
/// "?" for tentative, "×" for declined. Empty for unresponded or missing.
fn rsvp_marker(my_status: Option<&str>) -> &'static str {
    match my_status {
        Some("accepted")                                 => "•",
        Some("organizer")                                => "∘",
        Some("tentative") | Some("tentativelyAccepted") => "?",
        Some("declined")                                 => "×",
        _                                                => "",
    }
}

fn humanize_status(status: &str) -> &str {
    match status {
        "needsAction" => "Needs response",
        "accepted" => "Accepted",
        "declined" => "Declined",
        "tentative" | "tentativelyAccepted" => "Tentative",
        "confirmed" => "Confirmed",
        "cancelled" => "Cancelled",
        _ => status,
    }
}

fn clean_description(desc: &str) -> String {
    let desc = desc.to_string();
    // Strip HTML tags if it looks like HTML
    let desc = if desc.trim_start().starts_with('<') {
        let re = regex::Regex::new(r"<[^>]+>").unwrap();
        re.replace_all(&desc, " ")
            .replace("&nbsp;", " ")
            .replace("&amp;", "&")
            .replace("&lt;", "<")
            .replace("&gt;", ">")
            .to_string()
    } else {
        desc
    };

    // Clean garbage patterns
    let re_color = regex::Regex::new(r"BC\d+-Color:\s*-?\d+\s*").unwrap();
    let re_meet = regex::Regex::new(r"(?s)-::~:~::~:~.*$").unwrap();
    let re_underscore = regex::Regex::new(r"_{3,}").unwrap();
    let re_dashes = regex::Regex::new(r"-{5,}").unwrap();
    let re_box = regex::Regex::new(r"[\u{2501}\u{2550}\u{2500}]{3,}").unwrap();
    let re_blanks = regex::Regex::new(r"\n{3,}").unwrap();

    let desc = re_color.replace_all(&desc, "");
    let desc = re_meet.replace_all(&desc, "");
    let desc = re_underscore.replace_all(&desc, "");
    let desc = re_dashes.replace_all(&desc, "");
    let desc = re_box.replace_all(&desc, "");
    let desc = re_blanks.replace_all(&desc, "\n\n");
    desc.trim().to_string()
}

fn shellexpand(path: &str) -> String {
    if path.starts_with('~') {
        let home = config::home_dir();
        format!("{}{}", home.display(), &path[1..])
    } else {
        path.to_string()
    }
}

/// Pick the most useful meeting URL out of an event's description /
/// location blob. Priority order:
///   1. Modern Teams meet links     `https://teams.microsoft.com/meet/<id>?p=…`
///   2. Classic Teams meetup-join   `https://teams.microsoft.com/l/meetup-join/19%3a…`
///   3. Any Teams URL (msteams: scheme included)
///   4. Zoom join links             `https://*.zoom.us/j/<id>` (with optional ?pwd=)
///   5. Google Meet                 `https://meet.google.com/<id>`
///   6. Any https?:// URL — last-resort fallback
///
/// Returns the first hit; the calling site picks the launcher
/// (teams-for-linux for Teams URLs, xdg-open for the rest).
fn extract_meeting_url(haystack: &str) -> Option<String> {
    use regex::Regex;
    // Patterns anchor URLs against terminating characters (whitespace,
    // `>`, `"`, `'`, `<`, `]`) so we don't capture trailing markup
    // from html-formatted descriptions. The `tail` placeholder gets
    // substituted into each pattern.
    let tail = r#"[^\s<>"'\]]+"#;
    let patterns: [String; 7] = [
        format!(r"https://teams\.microsoft\.com/meet/{}", tail),
        format!(r"https://teams\.microsoft\.com/l/meetup-join/{}", tail),
        r#"msteams:[^\s<>"']+"#.to_string(),
        format!(r"https://teams\.microsoft\.com/{}", tail),
        format!(r"https://[a-zA-Z0-9.-]+\.zoom\.us/j/{}", tail),
        format!(r"https://meet\.google\.com/[a-z0-9-]+(?:\?{})?", tail),
        format!(r"https?://{}", tail),
    ];
    for p in &patterns {
        let re = Regex::new(p).ok()?;
        if let Some(m) = re.find(haystack) {
            // Strip a trailing `)` / `.` / `,` that often closes an
            // inline link in Markdown or Outlook-flavoured plain text.
            let mut s = m.as_str().to_string();
            while s.ends_with(')') || s.ends_with('.') || s.ends_with(',') {
                s.pop();
            }
            return Some(s);
        }
    }
    None
}

/// Pull the host out of a URL string. Returns the part between
/// `://` and the first `/` (or end-of-string). Lowercased so
/// host-suffix matching works regardless of how the URL was cased.
/// `msteams:` and other schemes without `://` return None.
fn url_host(url: &str) -> Option<String> {
    let after_scheme = url.split_once("://")?.1;
    let host = after_scheme.split('/').next()?;
    // Strip optional `user:pass@` and trailing `:port`.
    let host = host.rsplit_once('@').map(|(_, h)| h).unwrap_or(host);
    let host = host.split_once(':').map(|(h, _)| h).unwrap_or(host);
    Some(host.to_ascii_lowercase())
}

/// Cheap, dependency-free `which`: probe each `:`-separated PATH dir
/// for an executable file named `cmd`. We don't try to follow
/// symlinks or check exec bits exhaustively — `is_file()` plus the
/// path's existence is enough for the "is teams-for-linux installed"
/// gate the join flow needs.
fn which_on_path(cmd: &str) -> bool {
    let path = match std::env::var_os("PATH") { Some(p) => p, None => return false };
    for dir in std::env::split_paths(&path) {
        let candidate = dir.join(cmd);
        if candidate.is_file() { return true; }
    }
    false
}

/// Flush any pending bytes on stdin
fn flush_stdin() {
    use std::io::Read;
    unsafe {
        let flags = libc::fcntl(0, libc::F_GETFL);
        libc::fcntl(0, libc::F_SETFL, flags | libc::O_NONBLOCK);
        let mut buf = [0u8; 256];
        while std::io::stdin().read(&mut buf).unwrap_or(0) > 0 {}
        libc::fcntl(0, libc::F_SETFL, flags);
    }
}

// =========================================================================
// Main
// =========================================================================

/// One-shot: push a single local-only event to its remote (Google) calendar
/// and persist the returned external_id back. Returns process exit code.
fn push_event_oneshot(event_id: i64) -> i32 {
    let db = match Database::new(None) {
        Ok(d) => d,
        Err(e) => { eprintln!("could not open tock.db: {}", e); return 1; }
    };
    let evt = match db.get_event(event_id) {
        Ok(Some(e)) => e,
        Ok(None) => { eprintln!("event {} not found", event_id); return 1; }
        Err(e) => { eprintln!("db error: {}", e); return 1; }
    };
    let data = EventData {
        id: Some(evt.id),
        calendar_id: evt.calendar_id,
        external_id: evt.external_id.clone(),
        title: evt.title.clone(),
        description: evt.description.clone(),
        location: evt.location.clone(),
        start_time: evt.start_time,
        end_time: evt.end_time,
        all_day: evt.all_day,
        timezone: evt.timezone.clone(),
        recurrence_rule: evt.recurrence_rule.clone(),
        series_master_id: evt.series_master_id,
        status: evt.status.clone(),
        organizer: evt.organizer.clone(),
        attendees: evt.attendees.clone(),
        my_status: evt.my_status.clone(),
        alarms: evt.alarms.clone(),
        metadata: evt.metadata.clone(),
    };
    if data.external_id.is_some() {
        eprintln!("event {} already has external_id={:?}; skipping",
            evt.id, data.external_id);
        return 0;
    }
    let cal = match db.get_calendars(false).ok()
        .and_then(|cs| cs.into_iter().find(|c| c.id == data.calendar_id))
    {
        Some(c) => c,
        None => { eprintln!("calendar {} not found", data.calendar_id); return 1; }
    };
    if cal.source_type != "google" {
        eprintln!("calendar source_type={} (only google is supported here)", cal.source_type);
        return 1;
    }
    let cfg_str = match cal.source_config.as_ref() {
        Some(s) => s,
        None => { eprintln!("calendar source_config missing"); return 1; }
    };
    let cfg: serde_json::Value = match serde_json::from_str(cfg_str) {
        Ok(v) => v,
        Err(e) => { eprintln!("source_config parse: {}", e); return 1; }
    };
    let email = cfg.get("email").and_then(|v| v.as_str()).unwrap_or("");
    let safe_dir = cfg.get("safe_dir").and_then(|v| v.as_str());
    let google_cal_id = cfg.get("google_calendar_id").and_then(|v| v.as_str()).unwrap_or("");
    if email.is_empty() || google_cal_id.is_empty() {
        eprintln!("source_config missing email or google_calendar_id");
        return 1;
    }
    let mut gc = sources::google::GoogleCalendar::new(email, safe_dir);
    if gc.get_access_token().is_none() {
        eprintln!("Google auth failed: {:?}", gc.last_error);
        return 1;
    }
    println!("pushing event {} ('{}') to calendar {}...", evt.id, evt.title, google_cal_id);
    match gc.create_event(google_cal_id, &data) {
        Some(remote_id) => {
            let mut updated = data;
            updated.id = Some(evt.id);
            updated.external_id = Some(remote_id.clone());
            if let Err(e) = db.save_event(&updated) {
                eprintln!("created on Google ({}) but failed to persist external_id locally: {}",
                    remote_id, e);
                return 1;
            }
            println!("created on Google, id={} (persisted locally)", remote_id);
            0
        }
        None => {
            eprintln!("push failed: {:?}", gc.last_error);
            1
        }
    }
}

fn main() {
    // CLI: `tock --push-event <id>` pushes a single local-only event to its
    // remote calendar (one-shot, no TUI). Used to backfill events that were
    // created before remote write-back was wired.
    let args: Vec<String> = std::env::args().collect();
    if let Some(pos) = args.iter().position(|a| a == "--push-event") {
        if let Some(id_str) = args.get(pos + 1) {
            if let Ok(id) = id_str.parse::<i64>() {
                std::process::exit(push_event_oneshot(id));
            }
        }
        eprintln!("usage: tock --push-event <event_id>");
        std::process::exit(2);
    }

    Crust::init();
    Crust::set_app_identity("Tock");
    Crust::clear_screen();
    Cursor::hide();

    let mut app = App::new();

    app.load_events_for_range();

    // Watch incoming ICS files
    let cal_id = app.config.get_i64("default_calendar", 1);
    let incoming_count = ics::watch_incoming(&app.db, cal_id);
    if incoming_count > 0 {
        app.load_events_for_range();
    }

    app.render_all();

    // Start background poller
    let poller = poller::Poller::start(
        app.db.clone(),
        &app.config,
        app._poller_tx.clone(),
    );

    flush_stdin();

    let mut weather_date = today();
    // Notification alarms fire on minute precision (±1min window). No need
    // to recheck on every idle wake.
    let mut last_notify_minute: i64 = -1;

    while app.running {
        let key = Input::getchr(Some(2));
        if let Some(ref k) = key {
            app.handle_input(k);
        } else {
            // Idle: check poller
            if let Ok(poller::PollerEvent::NeedsRefresh) = app.poller_rx.try_recv() {
                app.load_events_for_range();
                app.render_all();
            }

            // Check notifications only when the wall-clock minute changes.
            let cur_minute = crate::database::now_secs() / 60;
            if cur_minute != last_notify_minute {
                last_notify_minute = cur_minute;
                let default_alarm = app.config.get_i64("notifications.default_alarm", 15);
                notifications::check_and_notify(&app.db, default_alarm);
            }

            // Refresh weather on new day
            let t = today();
            if weather_date != t {
                weather_date = t;
                app.weather_forecast.clear();
                app.weather_fetched_at = 0;
                app.load_events_for_range();
                app.render_all();
            }

            // Check heathrow goto file
            app.check_heathrow_goto();
        }
    }

    drop(poller);
    Cursor::show();
    Crust::cleanup();
}

/// A timed event that crosses two or more local midnights (touches ≥3 calendar
/// days) fully covers the middle day(s), so in the week grid it would fill every
/// slot of every column it spans — the classic "company entered a reminder as a
/// multi-day timed event" case (e.g. 6/22 10:00 → 6/30 10:30). Such spans are
/// lifted OUT of the time grid and drawn as a single banner bar above it, like
/// all-day events. Overnight events (one midnight crossing) stay in the grid.
fn is_background_span(evt: &Event, tz: i64) -> bool {
    if evt.all_day || evt.end_time <= evt.start_time {
        return false;
    }
    let (sy, sm, sd, _, _, _) = ts_to_parts(evt.start_time + tz);
    let (ey, em, ed, _, _, _) = ts_to_parts((evt.end_time - 1) + tz);
    day_diff((ey, em, ed), (sy, sm, sd)) >= 2
}

/// Pick which timed event to show for a half-hour slot.
///
/// Among the non-all-day events overlapping `[slot_start, slot_end)`, return the
/// one that started most recently (largest `start_time`). Multi-day background
/// spans are excluded — they render as banner bars above the grid, not in it, so
/// a grid slot only ever resolves to an event actually drawn there.
fn pick_timed_event_at_slot(events: &[Event], slot_start: i64, slot_end: i64) -> Option<&Event> {
    let tz = local_tz_offset_secs();
    events
        .iter()
        .filter(|e| !e.all_day && !is_background_span(e, tz)
            && e.start_time < slot_end && e.end_time > slot_start)
        .max_by_key(|e| e.start_time)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ev(id: i64, start_time: i64, end_time: i64) -> Event {
        Event {
            id,
            calendar_id: 1,
            external_id: None,
            title: format!("evt{}", id),
            description: None,
            location: None,
            start_time,
            end_time,
            all_day: false,
            timezone: None,
            recurrence_rule: None,
            series_master_id: None,
            status: "confirmed".into(),
            organizer: None,
            attendees: None,
            my_status: None,
            alarms: None,
            metadata: None,
            calendar_name: "Test".into(),
            calendar_color: 39,
        }
    }

    #[test]
    fn load_quotes_skips_yaml_frontmatter() {
        let dir = std::env::temp_dir().join("tock_quotes_test");
        let _ = std::fs::create_dir_all(&dir);
        let f = dir.join("quotes.md");
        std::fs::write(
            &f,
            "---\ncreated: 2026-06-11\ntags:\n  - personal\ntype: area\n---\n\n# 喜歡的話\n\n- 說明文字的 bullet 不該上牆\n- 按 `\"` 開練習框\n\n---\n\n- Real quote one. — A ｜ 中文\n- 純中文句不進英文練習池\n- Real quote two.\n",
        )
        .unwrap();
        let quotes = load_quotes(f.to_str().unwrap());
        assert_eq!(quotes.len(), 2);
        assert_eq!(quotes[0].en, "Real quote one. — A");
        assert_eq!(quotes[0].zh.as_deref(), Some("中文"));
        assert_eq!(quotes[1].en, "Real quote two.");
        let _ = std::fs::remove_file(&f);
    }

    #[test]
    fn char_diff_marks_typos_and_misses() {
        let t: Vec<char> = "stay hungry".chars().collect();
        // perfect
        let (hit, ok) = char_diff(&t, &t);
        assert!(hit.iter().all(|&b| b) && ok.iter().all(|&b| b));
        // typo: "stey" — 'a' missed in target, 'e' wrong in typed
        let typed: Vec<char> = "stey hungry".chars().collect();
        let (hit, ok) = char_diff(&t, &typed);
        assert_eq!(hit.iter().filter(|h| !**h).count(), 1);
        assert_eq!(ok.iter().filter(|o| !**o).count(), 1);
        // empty typed: everything missed, no extras
        let (hit, ok) = char_diff(&t, &[]);
        assert!(hit.iter().all(|&b| !b));
        assert!(ok.is_empty());
    }

    #[test]
    fn split_author_on_last_emdash() {
        let (q, a) = split_author("Stay hungry. — Steve Jobs, Stanford 2005");
        assert_eq!(q, "Stay hungry.");
        assert_eq!(a, Some("Steve Jobs, Stanford 2005"));
        let (q, a) = split_author("別斷 > 衝量。");
        assert_eq!(q, "別斷 > 衝量。");
        assert_eq!(a, None);
    }

    #[test]
    fn wrap_display_breaks_spaces_and_cjk() {
        // English wraps at word boundaries
        let lines = wrap_display("Stay hungry. Stay foolish.", 14);
        assert_eq!(lines, vec!["Stay hungry.", "Stay foolish."]);
        // Unspaced CJK (double-width) hard-breaks per character without overflow
        let lines = wrap_display("別斷大於衝量再忙也別歸零", 10);
        assert!(lines.iter().all(|l| display_width(l) <= 10));
        assert_eq!(lines.concat(), "別斷大於衝量再忙也別歸零");
        // Short input stays on one line
        assert_eq!(wrap_display("hello", 20), vec!["hello"]);
    }

    #[test]
    fn background_span_excluded_from_grid_picks() {
        // #224-style regression: an 11-day "background" reminder (id 1) overlapping
        // the whole day, plus a same-day 09:00-17:30 course (id 2). Day list is sorted
        // by start_time like the real one (background first, since it started earlier).
        // The background span is now rendered as a banner bar above the grid, so it
        // must NEVER be picked from a grid slot — only the same-day course resolves.
        let day = 1_781_568_000; // arbitrary midnight-ish epoch for the test day
        let bg = ev(1, day - 2 * 86400, day + 9 * 86400); // started 2 days before, ends 9 days later
        let course_start = day + 9 * 3600; // 09:00
        let course_end = day + 17 * 3600 + 1800; // 17:30
        let course = ev(2, course_start, course_end);
        let events = vec![bg, course];

        let pick = |s: i64| pick_timed_event_at_slot(&events, s, s + 1800).map(|e| e.id);

        // Outside the course (08:00 / 18:00): the background span is the only
        // overlap, but it's a banner now — grid resolves to nothing.
        assert_eq!(pick(day + 8 * 3600), None);
        assert_eq!(pick(day + 18 * 3600), None);
        // During the course: the same-day course resolves.
        assert_eq!(pick(course_start), Some(2));
        assert_eq!(pick(day + 14 * 3600), Some(2));
    }

    #[test]
    fn is_background_span_classifies_spans_not_overnighters() {
        let tz = 0; // test in UTC-equivalent terms
        let day = 1_781_568_000;
        // 8-day timed reminder (the reported case shape): banner.
        let long = ev(1, day + 10 * 3600, day + 8 * 86400 + 10 * 3600 + 1800);
        assert!(is_background_span(&long, tz));
        // Overnight 18:00 → next-day 09:00 (one midnight): stays in the grid.
        let overnight = ev(2, day + 18 * 3600, day + 86400 + 9 * 3600);
        assert!(!is_background_span(&overnight, tz));
        // Plain same-day meeting: stays in the grid.
        let meeting = ev(3, day + 9 * 3600, day + 10 * 3600);
        assert!(!is_background_span(&meeting, tz));
    }

    #[test]
    fn extract_modern_teams_meet() {
        let body = "Join: https://teams.microsoft.com/meet/31274339366591?p=10ubU0wL4gdnhyeK9w\nMeeting ID: 312";
        let url = extract_meeting_url(body).unwrap();
        assert!(url.starts_with("https://teams.microsoft.com/meet/31274339366591"));
        assert!(url.contains("?p=10ubU0wL4gdnhyeK9w"));
    }

    #[test]
    fn extract_classic_meetup_join() {
        let body = "System reference<https://teams.microsoft.com/l/meetup-join/19%3ameeting_OGNh@thread.v2/0?context=%7b%22Tid%22%3a%22012%22%7d>";
        let url = extract_meeting_url(body).unwrap();
        assert!(url.contains("/l/meetup-join/19%3ameeting_OGNh"));
        // Must not include the trailing > from the html-style link.
        assert!(!url.ends_with('>'));
    }

    #[test]
    fn modern_meet_link_beats_classic_when_both_present() {
        // Real outlook descriptions ship the modern `meet/` URL up
        // top and the classic `l/meetup-join` further down. The
        // first hit wins so we get the human-readable one.
        let body = "
            Join: https://teams.microsoft.com/meet/31274339366591?p=10ubU0w
            ...
            System reference: https://teams.microsoft.com/l/meetup-join/19%3a@thread.v2/0
        ";
        let url = extract_meeting_url(body).unwrap();
        assert!(url.contains("/meet/31274339366591"));
    }

    #[test]
    fn extract_zoom() {
        let body = "Please join: https://us02web.zoom.us/j/12345678?pwd=abc def";
        let url = extract_meeting_url(body).unwrap();
        assert!(url.starts_with("https://us02web.zoom.us/j/12345678"));
    }

    #[test]
    fn returns_none_when_no_url() {
        assert!(extract_meeting_url("Lunch at the canteen, no link").is_none());
        assert!(extract_meeting_url("").is_none());
    }

    #[test]
    fn url_host_extracts_lowercased_host() {
        assert_eq!(url_host("https://teams.microsoft.com/meet/123?p=x"),
                   Some("teams.microsoft.com".into()));
        assert_eq!(url_host("HTTPS://Teams.Microsoft.Com/x"),
                   Some("teams.microsoft.com".into()));
        assert_eq!(url_host("https://us02web.zoom.us/j/123"),
                   Some("us02web.zoom.us".into()));
        assert_eq!(url_host("https://user:pass@host.example.com:8080/p"),
                   Some("host.example.com".into()));
        assert_eq!(url_host("msteams:foo"), None);
        assert_eq!(url_host("not a url"), None);
    }
}
