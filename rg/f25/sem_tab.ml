
type form =
  | Var of int
  | Not of form
  | Or of form * form
  | Diamond of form

module Smart = struct
  let p i = Var i
  let n f = Not f
  let o f1 f2 = Or (f1, f2)
  let a f1 f2 = n (o (n f1) (n f2))
  let i f1 f2 = o (n f1) f2
  let ii f1 f2 = a (i f1 f2) (i f2 f1)
  let d f = Diamond f
  let b f = n (d (n f))
end

module Rtree = struct
  type 'a t = Node of 'a * 'a t list

  let to_string ?(unicode=true) string_of_inner t =
    let vline = if unicode then "│  " else "|  " in
    let sline = if unicode then "├──" else "|--" in
    let bline = if unicode then "└──" else "\\--" in
    let blank = "   " in
    let rec loop (Node (a, ts)) =
      string_of_inner a :: loop' [] ts
    and loop' prefix ts =
      let prefix_str =
        List.fold_left
          (fun acc b -> (if b then vline else blank) ^ acc)
          ""
          prefix
      in
      match ts with
      | [] -> []
      | [Node (a, ts)] ->
         [prefix_str ^ bline ^ string_of_inner a]
         @ loop' (false :: prefix) ts
      | Node (a, cs) :: ts ->
         [prefix_str ^ sline ^ string_of_inner a]
         @ loop' (true :: prefix) cs
         @ loop' prefix ts
    in
    String.concat "\n" (loop t)
end

module Model = struct
  type t = int list Rtree.t

  let rec string_of_vals vals =
    let rec go = function
      | [] -> ""
      | [v] -> "p" ^ string_of_int v
      | v :: vs -> "p" ^ string_of_int v ^ go vs
    in "{" ^ go vals ^ "}"

  let to_string = Rtree.to_string string_of_vals
end

type data =
  {
    true_forms : form list;
    false_forms : form list;
    true_vars : int list;
    false_vars : int list;
    true_next_forms : form list;
    false_next_forms : form list;
  }

let init true_forms false_forms =
  {
    true_forms;
    false_forms;
    true_vars = [];
    false_vars = [];
    true_next_forms = [];
    false_next_forms = [];
  }

let disjoint l r = List.(for_all (fun x -> not (mem x l)) r)

let all_some =
  let rec go = function
    | [] -> Some []
    | None :: _ -> None
    | Some x :: l -> Option.map (fun l -> x :: l) (go l)
  in go

let countermodel (f : form) : Model.t option =
  let rec go (data : data) : Model.t option =
    match data.false_forms with
    | f :: fs -> (
        match f with
        | Var i ->
          go { data with
               false_vars = i :: data.false_vars
             ; false_forms = fs;
             }
        | Not f ->
          go { data with
               true_forms = f :: data.true_forms
             ; false_forms = fs;
             }
        | Or (f1, f2) ->
          go { data with
               false_forms = f1 :: f2 :: fs;
             }
        | Diamond f ->
          go { data with
               false_next_forms = f :: data.false_next_forms;
               false_forms = fs;
             }
      )
    | [] -> (
        match data.true_forms with
        | f :: fs -> (
            match f with
            | Var i ->
              go { data with
                   true_vars = i :: data.true_vars;
                   true_forms = fs;
                 }
            | Not f ->
              go { data with
                   false_forms = f :: data.false_forms;
                   true_forms = fs
                 }
            | Or (f1, f2) -> (
                match go { data with true_forms = f1 :: fs } with
                | Some m -> Some m
                | None -> go { data with true_forms = f2 :: fs }
              )
            | Diamond f ->
              go { data with
                   true_next_forms = f :: data.true_next_forms;
                   true_forms = fs
                 }
          )
        | [] -> (
            if disjoint data.true_vars data.false_vars
            then
              let accs =
                List.map
                  (fun f -> go (init [f] data.false_next_forms))
                  data.true_next_forms
              in
              match all_some accs with
              | Some accs -> Some (Node (data.true_vars, accs))
              | None -> None
            else None
          )
      )
  in go (init [] [f])

module Example = struct
  (* □ p → □ □ p *)
  let f1 = Smart.(i (b (p 0)) (b (b (p 0))))

  (* □ (p → q) → ◇ p → ◇ q *)
  let f2 = Smart.(i (b (i (p 0) (p 1))) (i (d (p 0)) (d (p 1))))

  (* (◇ p → ◇ q) → □ (p → q) *)
  let f3 = Smart.(i (i (d (p 0)) (d (p 1))) (b (i (p 0) (p 1))))

  (* □ (p ∧ q) ↔ □ p ∧ □ q *)
  let f4 = Smart.(ii (b (a (p 0) (p 1))) (a (b (p 0)) (b (p 1))))

  (*  □ ◇ □ ◇ p → □ ◇ p *)
  let f5 = Smart.(i (b (d (b (d (p 0))))) (b (d (p 0))))

  (* □ ◇ p → ◇ p *)
  let f6 = Smart.(i (b (d (p 0))) (d (p 0)))

  (* ◇ ◇ p → ◇ p *)
  let f7 = Smart.(i (d (d (p 0))) (d (p 0)))

  (* □ (□ p → p) → □ p *)
  let f = Smart.(i (b (i (b (p 0)) (p 0))) (b (p 0)))

  let _ =
    match countermodel f with
    | Some m -> print_endline (Model.to_string m)
    | None -> print_endline "valid"
end
