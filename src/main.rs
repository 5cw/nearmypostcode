#![allow(non_upper_case_globals)]
#![allow(non_snake_case)]
/*

Program that converts the postcode database .csv file from the Office for National Statistics (ONS)
in to a packed binary format that is much more compact and quick to search. The packed format can
be read using the javascript library provided.

*/
use clap::{arg, command};
use std::collections::HashMap;
use std::fmt::Display;
use std::fmt::Formatter;
use std::fs::OpenOptions;
use std::io::{Seek, Write};
use std::num::ParseFloatError;
use std::process::ExitCode;
use std::u16;
use time::{Date, Time, UtcDateTime};

#[derive(Debug)]
pub enum PostcodeError {
    IOError(std::io::Error),
    InputMalformed(),
    InvalidFormat(),
    NotFound(),
}

#[derive(Debug, Clone, Copy, PartialEq)]
struct Point {
    x: f32,
    y: f32,
}

#[derive(Debug, Clone)]
struct PostcodeInfo {
    postcode: String,
    location: Point,
}

impl Display for PostcodeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        use PostcodeError::*;
        match self {
            IOError(e) => write!(f, "Error reading or writing postcode file: {e}"),
            InputMalformed() => write!(f, "Input file is not well formed"),
            InvalidFormat() => write!(f, "Postcode format not recognised"),
            NotFound() => write!(f, "Postcode is well-formed, but not known"),
        }
    }
}

impl From<std::io::Error> for PostcodeError {
    fn from(e: std::io::Error) -> Self {
        PostcodeError::IOError(e)
    }
}

impl From<ParseFloatError> for PostcodeError {
    fn from(_: ParseFloatError) -> Self {
        PostcodeError::InputMalformed()
    }
}

pub fn pack_code(code: &str) -> Result<[u8; 3], PostcodeError> {
    if code.len() < 7 {
        return Err(PostcodeError::InvalidFormat());
    }

    let mut chars = code.as_bytes().iter();

    fn encode_unit(x: u8) -> Result<u32, PostcodeError> {
        let mut x = x;
        if x >= b'A' && x <= b'Z' {
            for char in b"VOMKIC" {
                if x == *char {
                    return Err(PostcodeError::InvalidFormat());
                } else if x > *char {
                    x -= 1;
                }
            }
            Ok((x - b'A') as u32)
        } else {
            Err(PostcodeError::InvalidFormat())
        }
    }

    fn encode_AZ(x: u8) -> Result<u32, PostcodeError> {
        if x >= b'A' && x <= b'Z' {
            Ok((x - b'A') as u32)
        } else {
            Err(PostcodeError::InvalidFormat())
        }
    }

    fn encode_09(x: u8) -> Result<u32, PostcodeError> {
        if x >= b'0' && x <= b'9' {
            Ok((x - b'0') as u32)
        } else {
            Err(PostcodeError::InvalidFormat())
        }
    }

    fn encode_AZ09(x: u8) -> Result<u32, PostcodeError> {
        encode_AZ(x).or_else(|_| Ok(encode_09(x)? + 26))
    }

    fn encode_AZ09_space(x: u8) -> Result<u32, PostcodeError> {
        if x == b' ' {
            Ok(36)
        } else {
            encode_AZ(x).or_else(|_| Ok(encode_09(x)? + 26))
        }
    }

    // Skip the first two chars
    let _a = encode_AZ(*chars.next().unwrap())?;
    let _b = encode_AZ09(*chars.next().unwrap())?;

    // Encode the rest
    let c = 20 * 20 * 10 * 37 * encode_AZ09_space(*chars.next().unwrap())?;
    let d = 20 * 20 * 10 * encode_AZ09_space(*chars.next().unwrap())?;

    let e = 20 * 20 * encode_09(*chars.next().unwrap())?;
    let f = 20 * encode_unit(*chars.next().unwrap())?;
    let g = encode_unit(*chars.next().unwrap())?;
    let encoded = c + d + e + f + g;
    assert!(encoded < 2_u32.pow(24));
    let encoded = encoded.to_le_bytes();
    Ok([encoded[0], encoded[1], encoded[2]])
}

fn field_id(name: &str, headers: &Vec<&str>) -> Result<usize, PostcodeError> {
    match headers.iter().position(|n| *n == name) {
        Some(n) => Ok(n),
        None => Err(PostcodeError::InputMalformed()),
    }
}

fn parse_date(d: Option<&str>) -> Option<Date> {
    let d = d?;
    if d.len() < 6 {
        None
    } else {
        let y = d[0..4].parse().ok()?;
        let m: time::Month = d[4..6].parse::<u8>().ok()?.try_into().ok()?;
        let date = Date::from_calendar_date(y, m.into(), 1);
        Some(date.ok()?)
    }
}

fn read_postcodes(
    path: &str,
    exclude: &Vec<&str>,
) -> Result<(Vec<PostcodeInfo>, Point, Point, usize, usize, usize, u64), PostcodeError> {
    let file = OpenOptions::new().read(true).open(path)?;
    let mut pclist = Vec::new();
    let mut postcodes = csv::Reader::from_reader(file);
    let headers = postcodes.headers();
    if headers.is_err() {
        return Err(PostcodeError::InputMalformed());
    }
    let headers: Vec<&str> = headers.unwrap().iter().collect();
    let id_postcode = field_id("pcd", &headers)?;
    let id_lat = field_id("lat", &headers)?;
    let id_long = field_id("long", &headers)?;
    let id_date_intr = field_id("dointr", &headers)?;
    let id_date_term = field_id("doterm", &headers)?;

    let mut minlat = 9999.0f32;
    let mut maxlat = -9999.0f32;
    let mut minlong = 9999.0f32;
    let mut maxlong = -9999.0f32;

    let mut total = 0;
    let mut num_terminated = 0;
    let mut num_excluded = 0;

    let mut last_update = Date::from_ordinal_date(1970, 1).unwrap();

    'pcloop: for line in postcodes.records() {
        if line.is_err() {
            return Err(PostcodeError::InputMalformed());
        }
        total += 1;
        let line = line.unwrap();
        let postcode = line.get(id_postcode);
        if postcode.is_none() {
            continue;
        }
        let postcode = postcode.unwrap().to_string();
        let introduced = parse_date(line.get(id_date_intr));
        let terminated = parse_date(line.get(id_date_term));
        let is_current = match (introduced, terminated) {
            (Some(_), None) => true,
            _ => false,
        };
        if !is_current {
            num_terminated += 1;
            continue;
        }
        let lat = line.get(id_lat);
        if lat.is_none() {
            continue;
        }
        let lat: f32 = lat.unwrap().parse().unwrap();
        if lat > 99.0 {
            continue; // no location known
        }
        let long = line.get(id_long);
        if long.is_none() {
            continue;
        }
        let long: f32 = long.unwrap().parse().unwrap();
        let location = Point { x: long, y: lat };

        for prefix in exclude {
            if postcode.starts_with(prefix) {
                num_excluded += 1;
                continue 'pcloop;
            }
        }

        let introduced = introduced.unwrap();
        if introduced > last_update {
            last_update = introduced;
        }

        minlat = minlat.min(lat);
        maxlat = maxlat.max(lat);
        minlong = minlong.min(long);
        maxlong = maxlong.max(long);

        pclist.push(PostcodeInfo { postcode, location });
    }
    let skipped = total - pclist.len();
    let unixtime =
        UtcDateTime::new(last_update, Time::from_hms(0, 0, 0).unwrap()).unix_timestamp() as u64;
    Ok((
        pclist, // Postcodes
        Point {
            x: minlong,
            y: minlat,
        }, // Lower left corner of bounding box
        Point {
            x: maxlong,
            y: maxlat,
        }, // Upper right corner of bounding box
        skipped, // Number of postcodes skipped
        num_terminated, // number of postcodes terminated
        num_excluded, // number of postcodes terminated
        unixtime, // date of last update
    ))
}

fn calc_ll(minll: Point, maxll: Point, ll: Point) -> (u16, u16) {
    let latrange = maxll.y - minll.y;
    let longrange = maxll.x - minll.x;
    let lat = (((ll.y - minll.y) / latrange) * 65535.0).round() as u16;
    let long = (((ll.x - minll.x) / longrange) * 65535.0).round() as u16;
    (long, lat)
}

// enum DeltaPacked {
//     Absolute([u8; 8]),
//     DeltaP([u8; 5]),
//     DeltaLL([u8; 6]),
//     DeltaPLL([u8; 3]),
// }

// impl DeltaPacked {
//     fn write_to_file<W: Write>(&self, mut f: W) -> std::io::Result<usize> {
//         use DeltaPacked::*;
//         match self {
//             Absolute(a) => f.write(a),
//             DeltaP(a) => f.write(a),
//             DeltaLL(a) => f.write(a),
//             DeltaPLL(a) => f.write(a),
//         }
//     }

//     fn len(&self) -> usize {
//         use DeltaPacked::*;
//         match self {
//             Absolute(_) => 8,
//             DeltaP(_) => 5,
//             DeltaLL(_) => 6,
//             DeltaPLL(_) => 3,
//         }
//     }
// }

#[derive(Clone, Copy)]
struct ProcessedPostcode {
    long: i32,
    lat: i32,
    code_number: u32,
    prefix: [u8; 2],
}

fn process(
    pre: &PostcodeInfo,
    minll: Point,
    maxll: Point,
) -> Result<ProcessedPostcode, PostcodeError> {
    let (long, lat) = calc_ll(minll, maxll, pre.location);
    let this_prefix = [pre.postcode.as_bytes()[0], pre.postcode.as_bytes()[1]];
    let c = pack_code(&pre.postcode)?;
    let code_number = u32::from_le_bytes([c[0], c[1], c[2], 0]);
    Ok(ProcessedPostcode {
        long: long as i32,
        lat: lat as i32,
        code_number,
        prefix: this_prefix,
    })
}
fn pack_postcodes(
    postcodes: &Vec<PostcodeInfo>,
    minll: Point,
    maxll: Point,
) -> Result<(Vec<u8>, HashMap<String, u32>), PostcodeError> {
    let mut packed_codes = Vec::new();

    let mut lut: HashMap<String, u32> = HashMap::new();
    let processed: Vec<ProcessedPostcode> = postcodes
        .iter()
        .map(|x| process(x, minll, maxll).unwrap())
        .collect();

    let null_pcd = ProcessedPostcode {
        long: -0xFFFFFFF,
        lat: -0xFFFFFFF,
        code_number: 0,
        prefix: [0, 0],
    };
    // let mut dist_count = vec![0; 16];
    let mut lp = null_pcd;
    let mut last_point = 0;
    let mut run_index = -1;
    let mut i = 1;
    while i < processed.len() {
        let mut p = processed[i];
        if p.prefix != lp.prefix {
            // Any time the prefix changes, reset the previous code state.
            // This is important because the decoder skips to the start of
            // a prefix block as the first step, so it will still have the
            // initial state at this point.
            lp = null_pcd;
            last_point = 0;
            lp.prefix = p.prefix;
            lut.insert(
                String::from_utf8(p.prefix.to_vec()).unwrap(),
                packed_codes.len() as u32,
            );
        }
        while i + 1 < processed.len()
            && p.lat == processed[i + 1].lat
            && p.long == processed[i + 1].long
        {
            i += 1;
            p = processed[i];
        }
        let dlong = p.long - lp.long;
        let dlat = p.lat - lp.lat;
        let can_delta_encode_ll: bool = {
            let can_long = dlong >= -128 && dlong <= 127;
            let can_lat = dlat >= -128 && dlat <= 127;
            can_long && can_lat
        };
        let can_delta_half_encode_ll = {
            let can_long = dlong >= -8 && dlong <= 7;
            let can_lat = dlat >= -8 && dlat <= 7;
            can_long && can_lat
        };
        let latb = p.lat.to_le_bytes();
        let longb = p.long.to_le_bytes();
        let ll = [latb[0], latb[1], longb[0], longb[1]];
        let max_point = match processed.get(i + 1) {
            Some(nxt) => nxt.code_number - 1,
            None => p.code_number,
        } as i32;
        let dist = max_point as i32 - last_point as i32;
        // for power in 0..16 {
        //     if dlong.abs() >> power > 0 && dlat.abs() >> power > 0 {
        //         dist_count[power] += 1;
        //     }
        // }
        let (can_delta_encode_pc, pcdelta, point) = if dist <= 0 {
            // List is probably not sorted, inefficient
            (false, 0, max_point)
        } else if dist < 64 {
            (true, dist, max_point)
        // } else if (max_point - dist % 64) >= p.code_number as i32 && dist / 64 <= 64 {
        //     (true, (dist / 64 - 1) | 0x40, max_point - dist % 64)
        // } else if last_point + 64 * 64 >= p.code_number as i32
        //     && max_point + 1 > last_point + 64 * 64
        // {
        //     (true, 0x7F, last_point + 64 * 64)
        } else {
            (false, 0, max_point)
        };
        // let can_delta_mixed_half_encode = {
        //     let can_long = dlong >= -16 && dlong <= 15;
        //     let can_lat = dlat >= -16 && dlat <= 15;
        //     let can_pc = dist < 16 || !can_delta_encode_pc;
        //     can_long && can_lat && can_pc
        // };

        let c = max_point.to_le_bytes();
        let pcdelta = (pcdelta as u8).to_le_bytes()[0];
        let mut packed_entry: Vec<u8> = Vec::new();
        if pcdelta == 1 && can_delta_encode_ll {
            if run_index < 0 || packed_codes[run_index as usize] >= 0xFE {
                run_index = packed_codes.len() as i32;
                packed_entry.push(0xC0);
                // println!("begin")
            } else {
                packed_codes[run_index as usize] += 1;
                // println!("continue")
            }
        } else if can_delta_encode_pc {
            packed_entry.push(pcdelta);
        } else {
            packed_entry.push(if can_delta_half_encode_ll {
                0x40
            } else if can_delta_encode_ll {
                0x80
            } else {
                0x00
            });
            packed_entry.extend(c);
        }

        if can_delta_half_encode_ll && run_index < 0 {
            packed_entry.push((dlat & 0xF << 4 | dlong & 0xF) as u8)
        // } else if can_delta_mixed_half_encode {
        //     packed_entry[0] |= 0xC0 | (dlat & 0x18 << 1) as u8;
        //     packed_entry.push((dlat & 0x7 << 5 | dlong & 0x1F) as u8)
        } else if can_delta_encode_ll {
            packed_entry.extend([dlat.to_le_bytes()[0], dlong.to_le_bytes()[0]])
        } else {
            packed_entry.extend(ll)
        }

        packed_codes.extend(packed_entry);
        lp = p;
        i += 1;
        last_point = point;
    }
    // println!("{:?}", dist_count);
    Ok((packed_codes, lut))
}

fn human(n: u64) -> String {
    let mut n: f64 = n as f64;
    const names: [&str; 4] = ["Bytes", "KiB", "MiB", "GiB"];
    let mut ni = 0;
    while ni < names.len() - 1 && n > 1024.0 {
        ni += 1;
        n /= 1024.0;
    }
    format!("{:.3} {}", n, names[ni])
}

fn do_postcode_repack(
    infilename: &str,
    outfilename: &str,
    exclude: &Vec<&str>,
) -> Result<(), PostcodeError> {
    println!("Reading postcodes...");
    let (mut postcodes, minll, maxll, skipped, terminated, excluded, last_update) =
        read_postcodes(infilename, exclude)?;
    println!("  File contained {} entries.", postcodes.len() + skipped);
    println!("    {} of these were skipped.", skipped);
    println!(
        "      {} of the skips were for terminated postcodes.",
        terminated
    );
    println!(
        "      {} of the skips were for excluded prefixes.",
        excluded
    );
    println!(
        "  Will process {} postcodes in the bounding box from {},{} to {},{}",
        postcodes.len(),
        minll.x,
        minll.y,
        maxll.x,
        maxll.y
    );
    println!("Sorting postcode lists...");
    postcodes.sort_by(|a, b| a.postcode.cmp(&b.postcode));
    println!("Packing postcodes...");
    let (packed_codes, mut lut) = pack_postcodes(&postcodes, minll, maxll)?;
    let mut outfile = OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .open(outfilename)?;
    println!("Writing packed postcodes to file...");

    /*
    File structure:
    (all numbers in little endian unless specified otherwise)

    Header, 16 bytes:

        magic:   4 bytes "UKPP" - magic number for "UK Postcode Pack"
        version: 4 bytes (u32)  - version number of the file format (this code generates version 0x100)
        date:    8 bytes (u64)  - a unix epoch that represents the release date of the ONS dataset that the file was generated from

    Boudning box extents, 4*4 = 16 bytes:

        minlong: 4 bytes (f32)
        maxlong: 4 bytes (f32)
        minlat:  4 bytes (f32)
        maxlat:  4 bytes (f32)

    Quick lookup table, 26*36*4 = 3744 bytes:

        list of 26*36 index values
            position: 4 bytes (u32, byte offset into postcode data list)
        last_pos: 4 bytes (u32, conveniently is just above last entry in the table)

    Postcode data, variable length (3 to 8 bytes per postcode):

        list of postcodes:
            format:   2 bits
                00: u16 lat/long
                01: i4 delta lat/long
                10: i8 delta lat/long
                11: i5 delta lat/long
            lattop: 0 or 2 bits (present only if format is i5 delta, 2 MSB of latitude)
            postcode_delta: 4 or 6 bits (4 if format is i5 delta)
            postcode: 0 or 3 bytes (custom encoding, present only if postcode_delta == 0)
            lat/long:  1, 2, or 4 bytes (3 LSB of i5 lat, i5 long, 2 x i4, 2 x i8, or 2 x u16)

    */

    // Header...
    outfile.write(b"UKPP")?; // magic number is 1347439445

    // version 1 of file format
    const version: u32 = 0x100;
    outfile.write(&version.to_le_bytes())?;

    // data update date
    outfile.write(&last_update.to_le_bytes())?;

    // bounding box extents
    let minlong = minll.x;
    let maxlong = maxll.x;
    let minlat = minll.y;
    let maxlat = maxll.y;
    outfile.write(&minlong.to_le_bytes())?;
    outfile.write(&maxlong.to_le_bytes())?;
    outfile.write(&minlat.to_le_bytes())?;
    outfile.write(&maxlat.to_le_bytes())?;

    // Build the table in reverse to be able to calculate the offsets
    let mut lastpos = packed_codes.len() as u32;
    for c1 in (0..26).rev() {
        let s1 = b'A' + c1;
        for c2 in (0..36).rev() {
            let s2 = if c2 > 9 { b'A' + c2 - 10 } else { b'0' + c2 };
            let s_bytes = [s1, s2];
            let s = std::str::from_utf8(&s_bytes).unwrap().to_string();
            let pos = lut.get(&s).copied().unwrap_or(lastpos);
            lastpos = pos;
            lut.insert(s, pos);
        }
    }

    // Write it forwards, since that's the way the lookup will happen
    for c1 in 0..26 {
        let s1 = b'A' + c1;
        for c2 in 0..36 {
            let s2 = if c2 > 9 { b'A' + c2 - 10 } else { b'0' + c2 };
            let s_bytes = [s1, s2];
            let s = std::str::from_utf8(&s_bytes).unwrap().to_string();
            let pos = lut.get(&s).unwrap();
            outfile.write(&pos.to_le_bytes())?;
        }
    }

    // One extra element after end, total bytes
    outfile.write(&lastpos.to_le_bytes())?;
    outfile.write(&packed_codes)?;
    if let Ok(l) = outfile.stream_position() {
        println!("  Total file size: {}", human(l));
    } else {
        println!("  Non-fatal error: unable to determine final file size");
    }
    Ok(())
}

fn main() -> ExitCode {
    let matches = command!()
        .arg(arg!(<input> "Input file name (path to ONS Postcode Database CSV file)"))
        .arg(arg!(<output> "Output file name"))
        .arg(arg!(--exclude <prefix> ... "Exclude a group of postcodes by its prefix (can be specified multiple times)"))
        .get_matches();

    let infilename = &matches.get_one::<String>("input").expect("No input file");
    let outfilename = &matches.get_one::<String>("output").expect("No output file");
    let exclude = if let Some(e) = matches.get_many::<String>("exclude") {
        e.map(|a| a.as_str()).collect()
    } else {
        Vec::new()
    };

    match do_postcode_repack(infilename, outfilename, &exclude) {
        Err(e) => {
            eprintln!("Error repacking postcodes: {e}");
            ExitCode::FAILURE
        }
        Ok(_) => {
            println!("Complete");
            ExitCode::SUCCESS
        }
    }
}
