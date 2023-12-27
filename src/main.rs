use std::collections::HashMap;
use std::collections::HashSet;

#[derive(Clone)]
struct LogicPoint
{
    logic_point_inputs: Vec<String>,
    external_inputs: Vec<String>,
    value: bool,
    evaluated: bool,
    gate: String,
    expr_str: String,
    symb_str: String
}

impl LogicPoint {
    fn evaluate(&mut self, externals: HashMap<String, bool>, feed_forward: HashMap<String, LogicPoint>)
    {
        let mut values = Vec::new();
        let mut sigstr = "".to_string();
        let mut valstr = "".to_string();
        for signal in &self.external_inputs
        {
            sigstr += signal;
            sigstr += " ";
            sigstr += &self.gate;
            sigstr += " ";
            values.push(externals.get(signal).unwrap().clone());
        }
        for logic in &self.logic_point_inputs
        {
            sigstr += logic;
            sigstr += " ";
            sigstr += &self.gate;
            sigstr += " ";
            values.push(feed_forward.get(logic).unwrap().value.clone());
        }

        sigstr.pop();
        for _character in self.gate.chars()
        {
            sigstr.pop();
        }
        sigstr.pop();

        self.symb_str = sigstr;

        if self.gate == "AND".to_string()
        {
            let mut check = true;
            let mut expr_str = "".to_string();
            for bit in values
            {
                check &= bit;
                expr_str += &bit.to_string();
                expr_str += "&"
            }
            expr_str.pop();
            expr_str = "(".to_string() + &expr_str.to_string() + ")";
            self.expr_str = expr_str;
            self.value = check;
        }
        else if self.gate == "OR".to_string()
        {
            let mut check = false;
            let mut expr_str = "".to_string();
            for bit in values
            {
                check |= bit;
                expr_str += &bit.to_string();
                expr_str += "|"
            }
            expr_str.pop();
            expr_str = "(".to_string() + &expr_str.to_string() + ")";
            self.expr_str = expr_str;
            self.value = check;
        }
        else if self.gate == "XOR".to_string()
        {
            let mut check = false;
            let mut expr_str = "".to_string();
            for bit in values
            {
                check ^= bit;
                expr_str += &bit.to_string();
                expr_str += "^"
            }
            expr_str.pop();
            expr_str = "(".to_string() + &expr_str.to_string() + ")";
            self.expr_str = expr_str;
            self.value = check;
        }
        else if self.gate == "NAND".to_string()
        {
            let mut check = true;
            let mut expr_str = "".to_string();
            for bit in values
            {
                check &= bit;
                expr_str += &bit.to_string();
                expr_str += "↑"
            }
            expr_str.pop();
            expr_str = "(".to_string() + &expr_str.to_string() + ")";
            self.expr_str = expr_str;
            self.value = !check;
        }
        else
        {
            panic!("noooo");
        }

        self.evaluated = true;
    }
}

fn create_dep_tree(output_point: String, display_point: LogicPoint, logic_points: HashMap<String, LogicPoint>) -> Vec<String>
{
    let mut display_point = logic_points.get(&output_point.to_string()).unwrap();
    let mut found: HashSet<String> = HashSet::new();
    let mut order = Vec::new();
    let mut curr = Vec::new();

    curr.push(output_point.to_string());
    order.push(output_point.to_string());
    found.insert(output_point.to_string());

    for logic_input in display_point.logic_point_inputs.clone()
    {
        curr.push(logic_input.clone());
        order.push(logic_input.clone());
        found.insert(logic_input.clone());
    }

    let mut cstring = "[[{};__PLACEHOLDER_UNKNOWN_VAR__".to_string();
    while (!found.contains(&cstring.clone()) || !curr.is_empty())
    {
        cstring = curr.pop().unwrap();
        for logic_point in logic_points.get(&cstring.clone()).unwrap().logic_point_inputs.clone()
        {
            if !found.contains(&logic_point.clone())
            {
                curr.push(logic_point.clone());
                order.push(logic_point.clone());
            }
            found.insert(logic_point.clone());
        }
    }

    order.reverse();
    order
}

fn run_circuit(rsig: HashMap<String, Vec<bool>>,
               osig: HashMap<String, bool>,
               lg: HashMap<String, (String, Vec<String>)>,
               prnt: HashMap<String, String>,
               iterations: usize,
               print_debug: bool) -> Vec<HashMap<String, bool>>
{
    let mut signals: HashMap<String, bool> = HashMap::new();

    for (name, values) in rsig.clone()
    {
        signals.insert(name, values[0]);
    }
    for (name, value) in osig.clone()
    {
        signals.insert(name, value);
    }

    let mut logic_points: HashMap<String, LogicPoint> = HashMap::new();
    for (name, (gate, cdepset)) in lg.clone()
    {
        let mut lg_deps = cdepset.iter()
                                .filter(|item| lg.contains_key(&item.to_string()))
                                .map(|item| item.to_string()).collect();
        let mut sig_deps = cdepset.iter()
                                .filter(|item| !lg.contains_key(&item.to_string()))
                                .map(|item| item.to_string()).collect();

        logic_points.insert(name, LogicPoint {
            logic_point_inputs: lg_deps,
            external_inputs: sig_deps,
            value: false,
            evaluated: false,
            gate,
            expr_str: String::new(),
            symb_str: String::new()
        });
    }

    let mut output_points: HashMap<String, String> = HashMap::new();
    for (name, dep) in prnt
    {
        output_points.insert(name, dep.to_string());
    }

    let mut output_paths: HashMap<String, Vec<String>> = HashMap::new();
    let mut retval: Vec<HashMap<String, bool>> = Vec::new();

    for (output_name, output_point) in &mut output_points {
        if signals.contains_key(&output_point.to_string().to_string())
        {
            output_paths.insert(output_name.to_string(), vec![output_point.to_string().to_string()]);
            continue;
        }
        output_paths.insert(output_name.to_string(), create_dep_tree(output_point.clone(),
                                                                     logic_points.get(&output_point.to_string().to_string()).unwrap().clone(),
                                                                     logic_points.clone()));
    }
    for i in 0..iterations {

        for (name, value) in rsig.clone()
        {
            let csig = signals.entry(name).or_insert(false);
            let index = i % value.len();
            *csig = value[index];
        }

        let mut cret: HashMap<String, bool> = HashMap::new();
        for (output_name, output_path) in &mut output_paths {
            if print_debug
            {
                println!("Output {output_name} derives from: ");
            }
            for logic_gate in output_path
            {
                if logic_points.get(logic_gate).unwrap().evaluated
                {
                    continue;
                }

                let mut borrow_clone = logic_points.get(logic_gate).unwrap().clone();
                borrow_clone.evaluate(signals.clone(), logic_points.clone());
                if print_debug
                {
                    println!("\t{logic_gate}: {}", borrow_clone.value);
                    println!("\t\t{}", borrow_clone.symb_str);
                    println!("\t\t{}", borrow_clone.expr_str);
                }

                cret.insert(output_name.to_string(), borrow_clone.value.clone());
                logic_points.insert(logic_gate.clone(), borrow_clone);
            }
        }

        for (name, point) in logic_points.clone()
        {
            logic_points.insert(
                name,
                LogicPoint{
                    gate: point.gate,
                    logic_point_inputs: point.logic_point_inputs,
                    value: point.value,
                    external_inputs: point.external_inputs,
                    evaluated: false,
                    expr_str: String::new(),
                    symb_str: String::new()
                }
            );
        }

        retval.push(cret);
    }
    retval
}

use std::fs::File;
use std::hash::Hash;
use std::io::{prelude::*, BufReader};

fn parse_circuit_file(filepath: String) -> std::io::Result<(
HashMap<String, Vec<bool>>,HashMap<String, bool>,HashMap<String, (String, Vec<String>)>,HashMap<String, String>
)>
{
    let file = File::open(filepath)?;
    let reader = BufReader::new(file);

    let mut repeated_signals: HashMap<String, Vec<bool>> = HashMap::new();
    let mut signals: HashMap<String, bool> = HashMap::new();
    let mut gates: HashMap<String, (String, Vec<String>)> = HashMap::new();
    let mut displays: HashMap<String, String> = HashMap::new();

    for line in reader.lines() {
        let mut l = line?.clone();
        if l.is_empty()
        {
            continue;
        }

        let mut decl_init_split: Vec<&str> = l.split(":").collect();

        let mut declaration: Vec<&str> = decl_init_split[0].split_whitespace().collect();
        let mut initialization = decl_init_split[1].to_string();
        initialization = initialization.chars().filter(|c| !c.is_whitespace()).collect();

        let mut decltype = declaration[0].to_string();
        let mut varname = declaration[1].to_string();

        if decltype == "repeated_signal"
        {
            initialization.remove(0);
            initialization.pop();

            let mut signal: Vec<bool> = Vec::new();
            for item in initialization.split(",")
            {
                signal.push(item == "1");
            }
            repeated_signals.insert(varname, signal);
        }
        else if decltype == "signal"
        {
            signals.insert(varname, initialization == "1");
        }
        else if decltype == "result"
        {
            let mut value: Vec<&str> = initialization.split("(").collect();
            let mut deplist = value[1].to_string();
            deplist.pop();
            let mut dependencies: Vec<String> = deplist.split(",").map(|s| s.to_string()).collect();
            gates.insert(varname,  (value[0].chars().filter(|c| !c.is_whitespace()).collect(), dependencies));
        }
        else if decltype == "display"
        {
            displays.insert(varname,  initialization.clone());
        }
    }

    Ok((repeated_signals, signals, gates, displays))
}

use std::ops::Fn;
fn main() {
    let (rsig,osig,gate,prnt) =
            parse_circuit_file("src/test1.circuit".to_string()).unwrap();
    let res = run_circuit(rsig, osig, gate, prnt, 8, false);

    for out in res
    {
        for (i,j) in out
        {
            println!("{i}: {j}");
        }
    }
}
