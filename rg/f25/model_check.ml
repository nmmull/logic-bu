type form =
  | True
  | False
  | Var of int
  | Not of form
  | Or of form * form
  | And of form * form
  | Implies of form * form
  | Iff of form * form
  | Box of form
  | Diamond of form

module Smart = struct
  let v x = Var x                (* p *)
  let n f = Not f                (* ¬ ϕ *)
  let o f1 f2 = Or (f1, f2)      (* ϕ₁ ∨ ϕ₂ *)
  let a f1 f2 = And (f1, f2)     (* ϕ₁ ∧ ϕ₂ *)
  let i f1 f2 = Implies (f1, f2) (* ϕ₁ → ϕ₂ *)
  let iff f1 f2 = Iff (f1, f2)   (* ϕ₁ ↔ ϕ₂ *)
  let d f = Diamond f            (* ◇ ϕ *)
  let b f = Box f                (* □ ϕ *)
  let t = True                   (* ⊤ *)
  let f = False                  (* ⊥ *)
end

module Example = struct
  let e1 phi = Smart.(iff (d phi) (n (b (n phi)))) (* ◇ ϕ ↔ ¬ □ ¬ ϕ *)
  let e2 phi = Smart.(iff (b phi) (n (d (n phi)))) (* □ ϕ ↔ ¬ ◇ ¬ ϕ *)
end

let rec md = function
  | True | False | Var _ -> 0
  | Not f -> md f
  | And (f1, f2) | Or (f1, f2)
  | Implies (f1, f2) | Iff (f1, f2) -> max (md f1) (md f2)
  | Box f | Diamond f -> md f + 1

module Example = struct
  let p = 0
  let q = 1
  let r = 2

  (* ¬ (□ p ∧ ◇ ((p ∧ q) ∧ ¬ ◇ r)) *)
  let phi = Smart.(n (a (b (v p)) (d (a (a (v p) (v q)) (n (d (v r)))))))

  let _ = assert (md phi = 2)
end

module Finite_model = struct
  type 'a t =
    {
      acc : ('a * 'a list) list;
      vln : ('a * int list) list;
    }

  let accs m w = Option.value ~default:[] (List.assoc_opt w m.acc)
  let vlns m w = Option.value ~default:[] (List.assoc_opt w m.vln)

  let acc m w1 w2 = List.mem w2 (accs m w1)
  let vln m w p = List.mem p (vlns m w)

  let exists_acc f m w = List.exists f (accs m w)
  let forall_acc f m w = List.for_all f (accs m w)

  let rec eval m w = function
    | True -> true
    | False -> false
    | Var p -> vln m w p
    | Not f -> not (eval m w f)
    | And (f1, f2) -> eval m w f1 && eval m w f2
    | Or (f1, f2) -> eval m w f1 || eval m w f2
    | Implies (f1, f2) -> if eval m w f1 then eval m w f2 else true
    | Iff (f1, f2) -> eval m w f1 = eval m w f2
    | Box f -> forall_acc (fun w -> eval m w f) m w
    | Diamond f -> exists_acc (fun w -> eval m w f) m w
end

module Example = struct
  open Finite_model

  type world = W1 | W2 | W3 | W4

  let p = 0
  let q = 1

  let m =
    {
      acc =
        [
          W1, [W2; W3];
          W2, [W2; W4];
          W3, [W4];
        ];
      vln =
        [
          W2, [p];
          W3, [q];
          W4, [p;q];
        ]
    }

  let phi = Smart.(d (b (v p)))       (* ◇ □ p *)
  let psi = Smart.(b (i (v q) (v p))) (* □ (q → p) *)

  let _ =
    [
      assert (eval m W1 phi);
      assert (eval m W2 phi);
      assert (eval m W3 phi);
      assert (not (eval m W4 phi));
      assert (not (eval m W1 psi));
      assert (eval m W2 psi);
      assert (eval m W3 psi);
      assert (eval m W4 psi);
    ]
end
