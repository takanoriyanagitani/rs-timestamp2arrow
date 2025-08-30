use core::time::Duration;

use std::time::SystemTime;

use arrow::array::TimestampMicrosecondArray;

pub fn unixtime2unixtime_us(unixtime: f64) -> u64 {
    (unixtime * 1_000_000.0) as u64
}

pub fn unixtime_us2duration(unixtime_us: u64) -> Duration {
    Duration::from_micros(unixtime_us)
}

pub fn unixtime2duration(unixtime: f64) -> Duration {
    let microseconds = unixtime2unixtime_us(unixtime);
    Duration::from_micros(microseconds)
}

pub fn duration2micros(d: Duration) -> i64 {
    d.as_micros() as i64
}

pub fn usvalues2array<I>(us_values: I) -> TimestampMicrosecondArray
where
    I: IntoIterator<Item = i64>,
{
    TimestampMicrosecondArray::from_iter_values(us_values)
}

pub fn duration_to_array<I>(durations: I) -> TimestampMicrosecondArray
where
    I: IntoIterator<Item = Duration>,
{
    let micros = durations.into_iter().map(duration2micros);
    TimestampMicrosecondArray::from_iter_values(micros)
}

pub fn f64_to_array<I>(seconds: I) -> TimestampMicrosecondArray
where
    I: IntoIterator<Item = f64>,
{
    let micros = seconds
        .into_iter()
        .map(unixtime2unixtime_us)
        .map(|v| v as i64);
    TimestampMicrosecondArray::from_iter_values(micros)
}

pub fn systemtime2unixtime(s: SystemTime) -> Duration {
    s.duration_since(SystemTime::UNIX_EPOCH).unwrap_or_default()
}

pub fn systemtime2array<I>(s_times: I) -> TimestampMicrosecondArray
where
    I: IntoIterator<Item = SystemTime>,
{
    let d = s_times.into_iter().map(systemtime2unixtime);
    duration_to_array(d)
}

pub fn strings2array<P, I>(str2systime: P, s_times: I) -> TimestampMicrosecondArray
where
    P: Fn(&str) -> SystemTime,
    I: IntoIterator<Item = String>,
{
    let s = s_times.into_iter().map(|s| str2systime(&s));
    systemtime2array(s)
}

pub fn str2systime_chrono(rfc3339: &str) -> Option<SystemTime> {
    let dt_fixed: chrono::DateTime<_> = chrono::DateTime::parse_from_rfc3339(rfc3339).ok()?;
    Some(dt_fixed.into())
}

pub fn str2systime_chrono_default(rfc3339: &str) -> SystemTime {
    str2systime_chrono(rfc3339).unwrap_or(SystemTime::UNIX_EPOCH)
}

pub fn strings2array_chrono<I>(s_times: I) -> TimestampMicrosecondArray
where
    I: IntoIterator<Item = String>,
{
    strings2array(str2systime_chrono_default, s_times)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{Duration, UNIX_EPOCH};

    // ------------------------------------------------------------------
    // Helper: convert an `i64` microsecond value to a `TimestampMicrosecondArray`
    // ------------------------------------------------------------------
    #[test]
    fn test_usvalues2array() {
        let values: Vec<i64> = vec![0, 1_000_000, -5, 42_345_678];
        let arr = usvalues2array(values.iter().cloned());
        assert_eq!(arr.len(), 4);
        assert_eq!(arr.value(0), 0);
        assert_eq!(arr.value(1), 1_000_000);
        assert_eq!(arr.value(2), -5);
        assert_eq!(arr.value(3), 42_345_678);
    }

    // ------------------------------------------------------------------
    // Helper: duration <-> microseconds
    // ------------------------------------------------------------------
    #[test]
    fn test_duration2micros_and_back() {
        let d = Duration::new(3, 123_000_000); // 3.123 sec
        let micros = duration2micros(d);
        assert_eq!(micros, 3_123_000);
        let d_back = Duration::from_micros(micros as u64);
        assert_eq!(d_back, d);
    }

    #[test]
    fn test_unixtime2unixtime_us() {
        let sec = 1.234567_f64;
        let us = unixtime2unixtime_us(sec);
        assert_eq!(us, 1_234_567);
        assert_eq!(unixtime2unixtime_us(1.999999), 1_999_999);
    }

    #[test]
    fn test_unixtime2duration() {
        let sec = 2.0_f64;
        let d = unixtime2duration(sec);
        assert_eq!(d, Duration::from_secs(2));
    }

    // ------------------------------------------------------------------
    // Helpers that build arrays from various sources
    // ------------------------------------------------------------------
    #[test]
    fn test_duration_to_array() {
        let durations = [
            Duration::from_micros(0),
            Duration::from_secs(1),
            Duration::from_micros(42_345_678),
        ];
        let arr = duration_to_array(durations.iter().cloned());
        assert_eq!(arr.len(), 3);
        assert_eq!(arr.value(0), 0);
        assert_eq!(arr.value(1), 1_000_000);
        assert_eq!(arr.value(2), 42_345_678);
    }

    #[test]
    fn test_f64_to_array() {
        let secs = [0.0_f64, 1.234567, 2.0];
        let arr = f64_to_array(secs.iter().cloned());
        assert_eq!(arr.len(), 3);
        assert_eq!(arr.value(0), 0);
        assert_eq!(arr.value(1), 1_234_567);
        assert_eq!(arr.value(2), 2_000_000);
    }

    #[test]
    fn test_systemtime2array() {
        let times = [
            UNIX_EPOCH,
            UNIX_EPOCH + Duration::from_secs(1),
            UNIX_EPOCH + Duration::from_micros(42_345_678),
        ];
        let arr = systemtime2array(times.iter().cloned());
        assert_eq!(arr.len(), 3);
        assert_eq!(arr.value(0), 0);
        assert_eq!(arr.value(1), 1_000_000);
        assert_eq!(arr.value(2), 42_345_678);
    }

    // ------------------------------------------------------------------
    // String → SystemTime → array
    // ------------------------------------------------------------------
    #[test]
    fn test_strings2array_custom_parser() {
        // Parser that interprets the string as a number of seconds
        let parser = |s: &str| {
            s.parse::<u64>()
                .ok()
                .map(|secs| UNIX_EPOCH + Duration::from_secs(secs))
                .unwrap_or(UNIX_EPOCH)
        };

        let inputs = ["0".to_string(), "10".to_string(), "invalid".to_string()];
        let arr = strings2array(parser, inputs.iter().cloned());
        assert_eq!(arr.len(), 3);
        assert_eq!(arr.value(0), 0);
        assert_eq!(arr.value(1), 10_000_000);
        assert_eq!(arr.value(2), 0); // default for invalid input
    }

    // ------------------------------------------------------------------
    // Chrono based parsing
    // ------------------------------------------------------------------
    #[test]
    fn test_str2systime_chrono_valid() {
        let s = "2024-08-27T12:34:56Z";
        let sys = str2systime_chrono(s).expect("should parse");
        // Convert back using chrono to verify the same instant
        let chrono_dt: chrono::DateTime<chrono::Utc> = sys.into();
        assert_eq!(chrono_dt.to_rfc3339(), "2024-08-27T12:34:56+00:00");
    }

    #[test]
    fn test_str2systime_chrono_invalid() {
        assert!(str2systime_chrono("not-a-date").is_none());
    }

    #[test]
    fn test_str2systime_chrono_default() {
        let valid = "1970-01-01T00:00:01Z";
        let sys = str2systime_chrono_default(valid);
        assert_eq!(
            sys.duration_since(UNIX_EPOCH).unwrap(),
            Duration::from_secs(1)
        );

        let invalid = "xyz";
        let sys_default = str2systime_chrono_default(invalid);
        assert_eq!(sys_default, UNIX_EPOCH);
    }

    #[test]
    fn test_strings2array_chrono() {
        let inputs = [
            "1970-01-01T00:00:00Z".to_string(),
            "1970-01-01T00:00:01.123456Z".to_string(),
            "invalid".to_string(),
        ];
        let arr = strings2array_chrono(inputs.iter().cloned());
        assert_eq!(arr.len(), 3);
        assert_eq!(arr.value(0), 0);
        assert_eq!(arr.value(1), 1_123_456);
        assert_eq!(arr.value(2), 0); // invalid string defaults to epoch
    }
}
