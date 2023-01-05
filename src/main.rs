use splr::*;
use pbpsat::solpbp;
use pbpsat::PBP;

fn main() {

    // {(0,0,0), (1,1,0), (1,0,1)} \cap {(1,1,0), (1,1,1)} = {(1,1,0)} 
    // println!("4,-3,-5 where -1,1,1 <= 0, -1,-1,0 <= -2");
    match solpbp::solpbp(PBP {obj : vec![4,-3,-5], cstr : vec![vec![-1,1,1,0], vec![-1,-1,0,-2]]},2) {
        Ok(res) => println!("{}",res),
        Err(res) => println!("{}",res),
    }

}

use std::fs::File;
use std::io::{BufRead,BufReader};

pub fn readpbp(filename: String) -> Result<Vec<Vec<i32>>, String> {
    let file = File::open(filename).map_err(|_| "file open error")?;
    let reader = BufReader::new(&file);

    let mut clauses: Vec<Vec<i32>> = Vec::new();

    for line in reader.lines() {
        let line = line.map_err(|_| "read line error")?;
        let vec: Vec<&str> = line.split_whitespace().collect();
        //println!("{:?}", vec);
        if vec.len() == 0 {
            continue;
        }
        if vec[0] != "c" && vec.len() > 1 {
            clauses.push(vec.iter().map(|c| c.parse::<i32>()).collect::<Result<Vec<i32>,_>>().map_err(|_| "parse error")?);
        }

    }
    Ok(clauses)
}

#[test]
fn test() {
    println!("4,3,-3");
    solpbp::solpbp(PBP {obj : vec![4,3,-3], cstr : vec![]},2);

    println!("4,0,-3,-3");
    solpbp::solpbp(PBP {obj : vec![4,0,-3,-3], cstr : vec![]},3);

    println!("0,7,19,-13");
    solpbp::solpbp(PBP {obj : vec![0,7,19,-13], cstr : vec![]},4);
}

#[test]
fn test_cstr() {

    println!("4,-3,-4 where 1,1,1 <= -1");
    solpbp::solpbp(PBP {obj : vec![4,-3,-4], cstr : vec![vec![1,1,1,-1]]},2);

    println!("4,-3,-4 where 1,1,1 <= 0");
    solpbp::solpbp(PBP {obj : vec![4,-3,-4], cstr : vec![vec![1,1,1,0]]},2);

    println!("4,-3,-4 where 1,1,1 <= 1");
    solpbp::solpbp(PBP {obj : vec![4,-3,-4], cstr : vec![vec![1,1,1,1]]},2);

    println!("4,-3,-4 where 1,1,1 <= 2");
    solpbp::solpbp(PBP {obj : vec![4,-3,-4], cstr : vec![vec![1,1,1,2]]},2);

    println!("4,-3,-4 where 1,1,1 <= 3");
    solpbp::solpbp(PBP {obj : vec![4,-3,-4], cstr : vec![vec![1,1,1,3]]},2);

    println!("4,-3,-4 where 1,1,1 <= 4");
    solpbp::solpbp(PBP {obj : vec![4,-3,-4], cstr : vec![vec![1,1,1,4]]},2);

    println!("4,-3,-4 where -1,1,1 <= -1, ");
    solpbp::solpbp(PBP {obj : vec![4,-3,-4], cstr : vec![vec![-1,1,1,-1]]},2);

    println!("4,-3,-5 where -1,1,1 <= 0, ");
    solpbp::solpbp(PBP {obj : vec![4,-3,-5], cstr : vec![vec![-1,1,1,0]]},2);

    // {(0,0,0), (1,1,0), (1,0,1)} \cap {(1,1,0), (1,1,1)} = {(1,1,0)} 
    println!("4,-3,-5 where -1,1,1 <= 0, -1,-1,0 <= -2");
    solpbp::solpbp(PBP {obj : vec![4,-3,-5], cstr : vec![vec![-1,1,1,0], vec![-1,-1,0,-2]]},2);


}