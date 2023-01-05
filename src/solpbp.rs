use splr::*;

use std::time::{Instant};
use std::cmp;

use crate::*;

#[derive(Debug)]
pub struct Sorter {
    pub input : Vec<usize>,
    pub output : Vec<usize>,
    pub numcarr : usize,
}

pub fn solpbp(input:PBP, base: i32) -> Result<i32,String> {

    let n = input.obj.len();

    // [1,2,3,...,n]を受け取り
    // [n+1,n+2,...,2n]を定義
    // 1=-(n+1), 2=-(n+2), ..., n=-2n,
    let mut f : Vec<Vec<i32>> = vec![];
    // PBPの変数とその否定した変数の関係をCNFで記述
    mk_cons_qv_pbv(&mut f, n);

    // CNFの新しく作られる変数のID
    let mut vargen = n + n + 1;

    // cstrをCNFに
    // baseでの素因数分解をせず、生成するsorterをひとつにする
    for cstr_idx in 0..input.cstr.len() {

        let mut cstr = input.cstr[cstr_idx].clone();

        // a_1 x_1 + ... + a_n x_n <= u
        let mut objvars = Vec::<usize>::new();
        // p:負の数の積算
        let mut p = 0;
        for i in 0..n {
            let v = cstr[i];
            if v < 0 {
                objvars.push(i+1+n);
                p-=v;
            } else {
                objvars.push(i+1);
            }
        }
    
        // abscstr=abs(cstr)
        let mut abscstr = Vec::<i32>::new();
        for i in cstr.iter() {
            abscstr.push(i.abs());
        }

        // 不等式の右辺にpを足す
        let u = cstr.pop().unwrap();
        abscstr.pop();
        if u+p < 0 {
            return Err("Infeasible".to_string());
        }
        // 制約が自明で成り立つ場合、制約式を作らず次のステップへ
        let sum = abscstr.iter().fold(0, |sum, a| sum + a);
        if sum <= u+p {
            continue;
        }

        /*
        //係数をbaseで素因数分解
        let mut num_b = Vec::<Vec<i32>>::new();
        for i in cstrabscstr.iter() {
            let mut tmp = Vec::<i32>::new();
            let mut m = *i;
            if m == 0 {
                tmp.push(0);
            } else {
                while m > 0 {
                    tmp.push(m % base);
                    m /= base;
                }
            }
            num_b.push(tmp);
        }
        */
        let mut num_b = Vec::<Vec<i32>>::new();
        let mut max_coef = 0;
        for i in abscstr.iter() {
            num_b.push(vec![*i]);
            if max_coef < *i {
                max_coef = *i;
            }
        }
        //println!("bum_b {:?}",num_b);

        //sorter作成
        let mut sorter_lst = Vec::<Sorter>::new();
        
        mk_sorterlst(&mut sorter_lst, & num_b, &mut f, max_coef as usize, objvars, n, &mut vargen);

        f.append(&mut mk_0cons(&sorter_lst, 
            sorter_lst[sorter_lst.len() - 1].output.len()-((u+p) as usize)));
        
        //println!("{:?}",sorter_lst);
        //println!("zerop {}", sorter_lst[sorter_lst.len() - 1].output.len()-((u+p) as usize));

    }

    // 実行可能解があるか判定
    // ubはここで求めた実行可能解のobj値。min obj <= ub, 

    let mut satmodel = Vec::<i32>::new();
    let mut ub = 0;
    let mut solver_input = Vec::<Vec<i32>>::new();
    
    let start = Instant::now();
    solver_input = Vec::<Vec<i32>>::new();
    solver_input.append(&mut f.clone());
    match Certificate::try_from(solver_input) {
        Ok(Certificate::SAT(ans)) => {
            satmodel=ans;
        },
        Ok(Certificate::UNSAT) | Err(SolverError::Inconsistent) | Err(SolverError::EmptyClause) => {
            return Err("Infeasible".to_string());
        },
        Err(e) => panic!("UNKNOWN; {}", e),
    }

    let end = start.elapsed();
    println!("Cstr feasibility {}.{:03}sec", end.as_secs(), end.subsec_millis());

    for i in 0..n {
        //println!("{:?}",satmodel[i]);
        if satmodel[i] > 0 {
            ub += input.obj[i];
        } else {

        }
        //q = q + ((sorter_lst[i].output.len() - zeropos[i]) as i32) * base.pow(j);
        //println!("{}",q);
    }

    // objをCNFに

    let mut mat_n = input.obj.clone();
    let mut p = 0;

    // objから負の係数を除去。
    // objvars:objの変数リスト。負の係数がつく変数は、否定した変数に変換
    let mut objvars = Vec::<usize>::new();
    for i in 0..n {
        let v = input.obj[i];
        if v < 0 {
            objvars.push(i+1+n);
            p-=v;
        } else {
            objvars.push(i+1);
        }
    }
    
    // mat_m=abs(mat_n)
    let mut mat_m = Vec::<i32>::new();
    for i in mat_n.iter() {
        mat_m.push(i.abs());
    }
    
    //係数をbaseで素因数分解
    let mut num_b = Vec::<Vec<i32>>::new();
    for i in mat_m.iter() {
        let mut tmp = Vec::<i32>::new();
        let mut m = *i;
        if m == 0 {
            tmp.push(0);
        } else {
            while m > 0 {
                tmp.push(m % base);
                m /= base;
           }
        }
        num_b.push(tmp);
    }
    //println!("bum_b {:?}",num_b);

    //sorter作成
    let mut sorter_lst = Vec::<Sorter>::new();
    //let mut vargen = n + n + 1;
    mk_sorterlst(&mut sorter_lst, & num_b, &mut f, base as usize, objvars, n, &mut vargen);

    //println!("{:?}",sorter_lst);
    //println!("{:?}",f);

    //////////解探索開始
    // sorter 1個目の出力を上から順に0を制約として入れて、satを解く

    let mut zerop = 0;
    let mut res = true;

    // 実行可能解のobj値(ub)以下から解を探すようにsorter出力への0制約の位置を調整する
    // pbpの解は実行可能解のobj値(ub)以下なので、実行可能解特定後、

    let mut p_b = Vec::<i32>::new();
    let mut m;
    m = ub + p;
    if m == 0 {
        p_b.push(0);
    } else {
        while m > 0 {
            p_b.push(m % base);
            m /= base;
       }
    }
    zerop = match p_b.len().cmp(&sorter_lst.len()) {
        cmp::Ordering::Less => sorter_lst[sorter_lst.len() - 1].output.len(),
        cmp::Ordering::Equal => sorter_lst[sorter_lst.len() - 1].output.len() - (p_b[p_b.len()-1] as usize),
        cmp::Ordering::Greater => {        
            let mut tmp = 0;
            for i in 0..(p_b.len()-sorter_lst.len()+1) {
                tmp = tmp * base + p_b[p_b.len()-i-1];
            }
            sorter_lst[sorter_lst.len() - 1].output.len() - (tmp as usize)},
    };

    //println!("p {} p_b {:?} zerop {}", p, p_b, zerop);
    //println!("sl.len {} p_b.len {}", sorter_lst.len(), p_b.len());
    //println!("sl.last.len {}", sorter_lst[sorter_lst.len() - 1].output.len());

    //println!("vg {}",vargen);

    // 一度satを解き、付値を求める。必ずsatとなる。

    // 見つけた付値にあわせてsorter 1個目の出力の0位置を調整する。
    //zerop = sorter_lst[sorter_lst.len() - 1].output.len() - get_sorterouts(&sorter_lst, &satmodel)[0].unwrap();

    //println!("{:?}", satmodel);
    //println!("{:?}", get_sorterouts(&sorter_lst, &satmodel));
    //println!("{}", zerop);


    // sorter 1個目の出力を順に0を制約として入れて、sorter 1個目の出力の最小を求める。
    while res && zerop < sorter_lst[sorter_lst.len() - 1].output.len() {
        zerop += 1;
        let start = Instant::now();
        solver_input = Vec::<Vec<i32>>::new();
        solver_input.append(&mut f.clone());
        solver_input.append(&mut mk_0cons(&sorter_lst, zerop));
        match Certificate::try_from(solver_input) {
            Ok(Certificate::SAT(ans)) => {
                res=true;
                satmodel=ans;
                zerop = sorter_lst[sorter_lst.len() - 1].output.len() 
                - get_sorterouts(&sorter_lst, &satmodel)[0].unwrap();
            },
            Ok(Certificate::UNSAT) | Err(SolverError::Inconsistent) | Err(SolverError::EmptyClause) => {
                res=false;
            },
            Err(e) => panic!("s UNKNOWN; {}", e),
        }

        let end = start.elapsed();
        println!("1st {} {}.{:03}sec", res, end.as_secs(), end.subsec_millis());
        
    }
    
    if !res {
        zerop -= 1;
    }

    //println!("zerop {}", zerop);
    let mut vg;

    //sorter 2個目以降。各sorterの"出力の1の数 % base"をbase-1から0まで調べる。
    // unsatになれば、次のsorterの解析に移る。
    let mut zeropos = Vec::<Option<usize>>::new();

    for i in 1..(sorter_lst.len()) {
        if sorter_lst[sorter_lst.len() - 1 - i].output.is_empty() {
            zeropos.push(None);
            continue;
        }

        // unsat回数を削減するため、"出力の1の数 % base"がjj以下かを順に調べる。
        for j in 0..cmp::min(base as usize, sorter_lst[sorter_lst.len() - 1 - i].output.len()) {
            //println!("iter {}",j);
            let jj = cmp::min(base as usize, sorter_lst[sorter_lst.len() - 1 - i].output.len()) - j - 1;
            vg = vargen;
            solver_input = Vec::<Vec<i32>>::new();
            solver_input.append(&mut f.clone());
            //solver.add_formula(&mk_0cons(&sorter_lst,zerop));
            solver_input.append(&mut mk_0cons2(&sorter_lst, zerop));
            for k in 0..(zeropos.len()) {
                match zeropos[k] {
                    Some(mk) => {
                        solver_input.append(
                        &mut mk_0cons_mod(&sorter_lst, sorter_lst.len() - 1 - 1 - k,
                        mk as usize, base as usize, &mut vg));
                    },
                    None => continue,
                }
            }
            
            solver_input.append(&mut mk_0cons_mod_less(&sorter_lst, sorter_lst.len() - 1 - i, 
                (jj + 1) as usize, base as usize, &mut vg));

            //println!("{:?}",solver_input);
            let start = Instant::now();

            match Certificate::try_from(solver_input) {
                Ok(Certificate::SAT(ans)) => {
                    res=true;
                    satmodel=ans;
                },
                Ok(Certificate::UNSAT) | Err(SolverError::Inconsistent) | Err(SolverError::EmptyClause) => {
                    res=false;
                },
                Err(e) => panic!("s UNKNOWN; {}", e),
            }

            let end = start.elapsed();
            println!("{}th {} {}.{:03}sec", i+1, res, end.as_secs(), end.subsec_millis());

            if !res {
                zeropos.push(Some((jj + 1) as usize));
                break;
            } else {
                if jj==0 {
                    zeropos.push(Some(0));
                    break;
                }
            }
        }
        
    }
    
    println!("-----result-----");
    //println!("N = {:?}",mat_n);
    //println!("sorter_lst {:?}",sorter_lst);
    //println!("zeropos {} {:?}",sorter_lst[sorter_lst.len() - 1].output.len() - zerop, zeropos);
    print!("x =");
    for i in satmodel.iter().take(n) {
        print!(" {:?}",*i);
    }
    println!();
    //println!("full model {:?}",satmodel);
    
    //変数付値から、最小値の計算
    let mut q = 0;
    for i in 0..n {
        //println!("{:?}",satmodel[i]);
        if satmodel[i] > 0 {
            q += mat_n[i];
        } else {

        }
        //q = q + ((sorter_lst[i].output.len() - zeropos[i]) as i32) * base.pow(j);
        //println!("{}",q);
    }
    //println!("sorter_lst {:?}",sorter_lst);
    println!("min val = {}",q);
    Ok(q)
}

// PBPの変数とその否定した変数の関係をCNFで記述
pub fn mk_cons_qv_pbv(f : &mut Vec<Vec<i32>>, n : usize) {
    for i in 0..n {
        f.push(vec![(i+1) as i32,(i+1+n) as i32]);
        f.push(vec![-1*((i+1) as i32),-1*((i+1+n) as i32)]);
    }
}


pub fn mksorter(x: &mut Vec<(usize,usize)>, l: usize, h:usize) {
    if (h - l) >= 1 {
        let mid = l + ((h - l) / 2);
        mksorter(x, l, mid);
        mksorter(x, mid + 1, h);
        sorter_merge(x, l, h, 1);
    }
}

fn compare_and_swap(x: &mut Vec<(usize,usize)>, a:usize, b:usize) { 
    x.push((a,b));
}
fn sorter_merge(x: &mut Vec<(usize,usize)>, l:usize, h:usize, r:usize) {
    let step = r * 2;
    if step < h - l {
        sorter_merge(x, l, h, step);
        sorter_merge(x, l + r, h, step);
        let mut i = l + r;
        while i < h - r {
            compare_and_swap(x, i, i + r);
            i += step;
        }
    } else {
        compare_and_swap(x, l, l + r);
    }
}

pub fn mk_sorterlst(sorter_lst: &mut Vec<Sorter>, num_b: &Vec<Vec<i32>>, 
    g: &mut Vec<Vec<i32>>, base: usize, vars : Vec<usize>, n: usize, vargen: &mut usize) {

    let mut carr = Vec::<usize>::new();

    for i in 0..(num_b.iter().fold(0, |max, a| if max < a.len() {a.len()} else {max})) {
        let cn = carr.len();
        let mut inp = carr;

        //let mut oup = Vec::<usize>::new();
        for j in 0..(num_b.len()) {
            if num_b[j].len() > i {
                for _k in 0..(num_b[j][i]) {
                    inp.push(vars[j]);
                }
            }
        }

        let j = inp.len();
        let mut ve = Vec::<(usize,usize)>::new();
        mksorter(&mut ve, 0, j.next_power_of_two() - 1);
        //println!("ve {:?}", ve);

        let mut layer = inp.clone();
        for _k in j..(j.next_power_of_two()) {
            layer.push(0);
            //inp.push(0);
        }
        //println!("inp {:?}",inp);
        for k in ve.iter() {
            let in0 = (*k).0;
            let in1 = (*k).1;

            if layer[in0] == 0 && layer[in1] == 0 {
                continue;
            } else if layer[in0] == 0 {
                layer[in0] = layer[in1];
                layer[in1] = 0;
            } else if layer[in1] == 0 {
                continue;
            } else {
                let newo1 = *vargen as isize;
                *vargen += 1;
                let newo2 = *vargen as isize;
                *vargen += 1;
                let oldi1 = layer[in0] as isize;
                let oldi2 = layer[in1] as isize;
                // oldi1 and oldi2 = newo2
                // oldi1 or oldi2 = newo1
                g.push(vec![(-oldi1) as i32, (-oldi2) as i32, newo2 as i32]);
                g.push(vec![oldi1 as i32, (-newo2) as i32]);
                g.push(vec![oldi2 as i32, (-newo2) as i32]);

                g.push(vec![oldi1 as i32, oldi2 as i32, (-newo1) as i32]);
                g.push(vec![(-oldi1) as i32, newo1 as i32]);
                g.push(vec![(-oldi2) as i32, newo1 as i32]);

                layer[in0]=newo1 as usize;
                layer[in1]=newo2 as usize;
            }
            //println!("{:?}",layer);

        }

        let mut oup = Vec::<usize>::new();
        for k in layer.iter().take(inp.len()) {
            oup.push(*k);
        }

        carr = Vec::<usize>::new();
        for k in 0..(j / (base as usize)) {
            carr.push(oup[(k + 1) * (base as usize) - 1]);
        }
        sorter_lst.push(Sorter {input:inp, output:oup, numcarr:cn});
    }
}

// 一番外(高い桁を扱う)のsorterが、zerop個以上、0を出力する、という制約を生成。
// zerop : 出力の0の個数
pub fn mk_0cons(stlst:& Vec<Sorter>, zeropos:usize) -> Vec<Vec<i32>> {
    let mut h = Vec::<Vec<i32>>::new();
    for j in 0..zeropos {
        let k = stlst[stlst.len() - 1].output.len() - j - 1;
        h.push(vec![-(stlst[stlst.len() - 1].output[k] as i32)]);
        //println!("{}", sorter_lst[i].output[k]);
    }
    //println!("0 assigns {:?}",h);
    h
}

//sorter2個目以降の解探索時に使う、1個目の出力を埋める関数
pub fn mk_0cons2(stlst:& Vec<Sorter>, zeropos:usize) -> Vec<Vec<i32>> {
    let mut h = Vec::<Vec<i32>>::new();
    for j in 0..zeropos {
        let k = stlst[stlst.len() - 1].output.len() - j - 1;
        h.push(vec![-(stlst[stlst.len() - 1].output[k] as i32)]);
        //println!("{}", sorter_lst[i].output[k]);
    }
    
    for j in zeropos..(stlst[stlst.len() - 1].output.len()) {
        let k = stlst[stlst.len() - 1].output.len() - j - 1;
        h.push(vec![stlst[stlst.len() - 1].output[k] as i32]);
    }
    //println!("0 assigns {:?}",h);
    h
}

// pos番目のsorterの"出力の1の数 % base"がlとなるかを表す制約を作る。
pub fn mk_0cons_mod(stlst:&[Sorter], pos: usize, l: usize, base: usize, vargen: &mut usize) -> Vec<Vec<i32>> {
    let mut h = Vec::<Vec<i32>>::new();
    let mut j = l;
    if l == 0 {
        
        let mut vl = vec![-(stlst[pos].output[0] as i32)];
        j += base;
        while j < stlst[pos].output.len() {
            let k1 = j;
            let k0 = j - 1;
            let v1 = stlst[pos].output[k1] as i32;
            let v0 = stlst[pos].output[k0] as i32;
            let o = (*vargen) as i32;
            *vargen += 1;
            vl.push(o);
            //v0 = true, v1 = false,
            //o = !v1 and v0
            h.push(vec![v1, -v0, o]);
            h.push(vec![-v1, -o]);
            h.push(vec![v0, -o]);
            j += base;
        }
        if j == stlst[pos].output.len() {vl.push(stlst[pos].output[j - 1] as i32);}
        h.push(vl);
    } else {
        let mut vl = Vec::<i32>::new();
        while j < stlst[pos].output.len() {
            let k1 = j;
            let k0 = j - 1;
            let v1 = stlst[pos].output[k1] as i32;
            let v0 = stlst[pos].output[k0] as i32;
            let o = (*vargen) as i32;
            *vargen += 1;
            vl.push(o);
            //v0 = true, v1 = false,
            //o = !v1 and v0
            h.push(vec![v1, -v0, o]);
            h.push(vec![-v1, -o]);
            h.push(vec![v0, -o]);
            j += base;
        }
        if j == stlst[pos].output.len() {vl.push(stlst[pos].output[j - 1] as i32);}
        h.push(vl);
        
    }
    //println!("h {:?}", h);
    h
}


// pos番目のsorterの"出力の1の数 % base"がl未満となるかを表す制約を作る。
pub fn mk_0cons_mod_less(stlst:&[Sorter], pos: usize, l: usize, base: usize, vargen: &mut usize) -> Vec<Vec<i32>> {
    let mut h = Vec::<Vec<i32>>::new();
    let mut j;

    let mut vl = Vec::<i32>::new();

    for m in 0..l {
        //println!("iter {} in mk mod less",m);
        j = m;
        if m == 0 {
            vl.push(-(stlst[pos].output[0] as i32));
            j += base;
            while j < stlst[pos].output.len() {
                let k1 = j;
                let k0 = j - 1;
                let v1 = stlst[pos].output[k1] as i32;
                let v0 = stlst[pos].output[k0] as i32;
                let o = (*vargen) as i32;
                *vargen += 1;
                vl.push(o);
                //v0 = true, v1 = false,
                //o = !v1 and v0
                h.push(vec![v1, -v0, o]);
                h.push(vec![-v1, -o]);
                h.push(vec![v0, -o]);
                j += base;
            }
            if j == stlst[pos].output.len() {vl.push(stlst[pos].output[j - 1] as i32);}
        } else {
            while j < stlst[pos].output.len() {
                let k1 = j;
                let k0 = j - 1;
                let v1 = stlst[pos].output[k1] as i32;
                let v0 = stlst[pos].output[k0] as i32;
                let o = (*vargen) as i32;
                *vargen += 1;
                vl.push(o);
                //v0 = true, v1 = false,
                //o = !v1 and v0
                h.push(vec![v1, -v0, o]);
                h.push(vec![-v1, -o]);
                h.push(vec![v0, -o]);
                j += base;
            }
            if j == stlst[pos].output.len() {vl.push(stlst[pos].output[j - 1] as i32);}
        }
    }
    h.push(vl);
    //println!("h {:?}", h);
    h
}

pub fn get_sorterouts(sorter_lst: & Vec<Sorter>, model: &[i32]) -> Vec<Option<usize>> {
    let mut ret = Vec::<Option<usize>>::new();
    for i in 0..(sorter_lst.len()) {
        if sorter_lst[sorter_lst.len() - 1 - i].output.is_empty() {
            ret.push(None);
        } else {
            let mut l = sorter_lst[sorter_lst.len() - 1 - i].output.len();
            for j in 0..(sorter_lst[sorter_lst.len() - 1 - i].output.len()) {
                let k = sorter_lst[sorter_lst.len() - 1 - i].output[j];
                if model[k - 1] == -(k as i32) {
                    l = j;
                    break;
                }
            }
            ret.push(Some(l));
        }
    }
    ret
}
