-- Prove2me | solution 1 for LatticePrepro.ThreeSAT.mem_language_iff
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:28:19.234995+00:00
-- url     : https://prove2.me/submissions/eef1491d-d15b-4db2-8905-62585d0d54a8

import Mathlib
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Verifier_Gates
import Definitions.Def_LatticePrepro_Verifier_Circuit
import Definitions.Def_LatticePrepro_Verifier_Expr
import Definitions.Def_LatticePrepro_Verifier_ThreeSAT

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.GateList end LatticePrepro.GateList
namespace LatticePrepro.ThreeSAT end LatticePrepro.ThreeSAT

namespace LatticePrepro

namespace BoolCircuit

variable (C : BoolCircuit)

lemma evalAux_input (x : Fin C.n → Bool) (wit : Fin C.w → Bool) {i : ℕ} (h : i < C.n) :
    C.evalAux x wit i = x ⟨i, h⟩ := by
  rw [evalAux]; simp [h]

lemma evalAux_wit (x : Fin C.n → Bool) (wit : Fin C.w → Bool) {i : ℕ} (h1 : C.n ≤ i)
    (h2 : i < C.n + C.w) : C.evalAux x wit i = wit ⟨i - C.n, by omega⟩ := by
  rw [evalAux]
  have h1' : ¬ i < C.n := by omega
  simp [h1', h2]

lemma evalAux_gate (x : Fin C.n → Bool) (wit : Fin C.w → Bool) (k : Fin C.g) :
    C.evalAux x wit (C.n + C.w + k.val) =
      C.gateFn k (C.evalAux x wit (C.gateIn k).1.val) (C.evalAux x wit (C.gateIn k).2.val) := by
  obtain ⟨kv, hkv⟩ := k
  rw [evalAux]
  have h1 : ¬ (C.n + C.w + kv < C.n) := by omega
  have h2 : ¬ (C.n + C.w + kv < C.n + C.w) := by omega
  have h3 : C.n + C.w + kv < C.n + C.w + C.g := by omega
  simp only [h1, h2, h3, ↓reduceDIte]
  have e : (⟨C.n + C.w + kv - (C.n + C.w), by omega⟩ : Fin C.g) = ⟨kv, hkv⟩ := Fin.ext (by simp)
  exact congrArg (fun k : Fin C.g =>
    C.gateFn k (C.evalAux x wit (C.gateIn k).1.val) (C.evalAux x wit (C.gateIn k).2.val)) e

end BoolCircuit

end LatticePrepro

namespace LatticePrepro

namespace BExpr

variable {L : ℕ}

lemma eval_bigAnd (ρ : Fin L → Bool) (l₀ : Fin L) (l : List (BExpr L)) :
    eval ρ (bigAnd l₀ l) = l.all (eval ρ) := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

end BExpr

namespace GateList

/-- The value of wire `i`: leaves `i < base` are read from `ρ`, wire `base + k` carries gate `k`
applied to the values of its input wires, and wires beyond the list (or gates reading a wire
that is not earlier) evaluate to `false`. -/
def evalWire (base : ℕ) (ρ : Fin base → Bool) (gs : List GateSpec) (i : ℕ) : Bool :=
  if h : i < base then ρ ⟨i, h⟩
  else
    match gs[i - base]? with
    | none => false
    | some g =>
      if _h : g.in1 < i ∧ g.in2 < i then g.fn (evalWire base ρ gs g.in1) (evalWire base ρ gs g.in2)
      else false
termination_by i
decreasing_by
  · exact _h.1
  · exact _h.2

variable {base : ℕ} (ρ : Fin base → Bool) (gs : List GateSpec)

lemma evalWire_of_lt {i : ℕ} (h : i < base) : evalWire base ρ gs i = ρ ⟨i, h⟩ := by
  rw [evalWire]
  simp [h]

lemma evalWire_of_none {i : ℕ} (h : base ≤ i) (hg : gs[i - base]? = none) :
    evalWire base ρ gs i = false := by
  rw [evalWire]
  simp [not_lt.mpr h, hg]

lemma evalWire_of_some {i : ℕ} (h : base ≤ i) {g : GateSpec} (hg : gs[i - base]? = some g) :
    evalWire base ρ gs i =
      if g.in1 < i ∧ g.in2 < i then g.fn (evalWire base ρ gs g.in1) (evalWire base ρ gs g.in2)
      else false := by
  conv_lhs => rw [evalWire]
  simp only [not_lt.mpr h, ↓reduceDIte, hg]
  split_ifs <;> rfl

/-- Appending gates does not change the values of the existing wires. -/
lemma evalWire_append (gs' : List GateSpec) {i : ℕ} (hi : i < base + gs.length) :
    evalWire base ρ (gs ++ gs') i = evalWire base ρ gs i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases h : i < base
    · rw [evalWire_of_lt ρ _ h, evalWire_of_lt ρ _ h]
    · have h' : base ≤ i := not_lt.mp h
      have hget : (gs ++ gs')[i - base]? = gs[i - base]? :=
        List.getElem?_append_left (by omega)
      rcases hg : gs[i - base]? with _ | g
      · rw [evalWire_of_none ρ _ h' (hget.trans hg), evalWire_of_none ρ _ h' hg]
      · rw [evalWire_of_some ρ _ h' (hget.trans hg), evalWire_of_some ρ _ h' hg]
        split_ifs with h12
        · rw [ih _ h12.1 (by omega), ih _ h12.2 (by omega)]
        · rfl

end GateList

namespace BExpr

open GateList

variable {base : ℕ}

/-- The result wire of a compiled expression carries its value. -/
lemma evalWire_compile (ρ : Fin base → Bool) (e : BExpr base) (gs : List GateSpec) :
    evalWire base ρ (compile base e gs).1 (compile base e gs).2 = e.eval ρ := by
  induction e generalizing gs with
  | leaf i => rw [compile, evalWire_of_lt ρ _ i.isLt, eval_leaf]
  | gate f a b iha ihb =>
    simp only [compile, eval_gate]
    set r₁ := compile base a gs with hr₁
    set r₂ := compile base b r₁.1 with hr₂
    have hlen : r₁.1.length ≤ r₂.1.length := (compile_fst_prefix b r₁.1).length_le
    have h1' : r₁.2 < base + r₁.1.length := compile_snd_lt a gs
    have h1 : r₁.2 < base + r₂.1.length := by omega
    have h2 : r₂.2 < base + r₂.1.length := compile_snd_lt b r₁.1
    have hget : (r₂.1 ++ [(⟨r₁.2, r₂.2, f⟩ : GateSpec)])[base + r₂.1.length - base]? =
        some ⟨r₁.2, r₂.2, f⟩ := by
      rw [Nat.add_sub_cancel_left, List.getElem?_append_right le_rfl, Nat.sub_self]
      rfl
    rw [evalWire_of_some ρ _ (Nat.le_add_right _ _) hget]
    simp only [h1, h2, and_self, ↓reduceIte]
    rw [evalWire_append ρ _ _ h1, evalWire_append ρ _ _ h2, hr₂, ihb]
    obtain ⟨t, ht⟩ := compile_fst_prefix b r₁.1
    rw [← ht, evalWire_append ρ _ _ (compile_snd_lt a gs), iha]

/-- `Fin.append` on an index below `n`. -/
lemma append_mk_of_lt {n w : ℕ} (x : Fin n → Bool) (wit : Fin w → Bool) {i : ℕ} (h : i < n)
    (h' : i < n + w) : Fin.append x wit ⟨i, h'⟩ = x ⟨i, h⟩ :=
  Fin.append_left x wit ⟨i, h⟩

/-- `Fin.append` on an index at least `n`. -/
lemma append_mk_of_le {n w : ℕ} (x : Fin n → Bool) (wit : Fin w → Bool) {i : ℕ} (h : n ≤ i)
    (h' : i < n + w) : Fin.append x wit ⟨i, h'⟩ = wit ⟨i - n, Nat.sub_lt_left_of_lt_add h h'⟩ := by
  have := Fin.append_right x wit ⟨i - n, Nat.sub_lt_left_of_lt_add h h'⟩
  rw [← this]
  congr 1
  ext
  simp only [Fin.natAdd_mk]
  omega

variable {n w : ℕ} (e : BExpr (n + w)) (he : 0 < e.size)

lemma toCircuit_outW : (toCircuit n w e he).outW = (compile (n + w) e []).2 := by
  show n + w + ((compile (n + w) e []).2 - (n + w)) = _
  have h1 := compile_snd_add_one he (base := n + w) []
  have h2 := length_compile_fst e []
  omega

/-- The circuit of an expression evaluates its wires as the compiled gate list does. -/
lemma evalAux_toCircuit (x : Fin n → Bool) (wit : Fin w → Bool) (i : ℕ) :
    (toCircuit n w e he).evalAux x wit i =
      evalWire (n + w) (Fin.append x wit) (compile (n + w) e []).1 i := by
  set gs := (compile (n + w) e []).1 with hgs
  have hwf : WF (n + w) gs := compile_wf e (WF.nil _)
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases h1 : i < n
    · rw [(toCircuit n w e he).evalAux_input x wit h1, evalWire_of_lt _ _ (by omega),
        append_mk_of_lt x wit h1]
    by_cases h2 : i < n + w
    · rw [(toCircuit n w e he).evalAux_wit x wit (not_lt.mp h1) h2, evalWire_of_lt _ _ h2,
        append_mk_of_le x wit (not_lt.mp h1)]
    by_cases h3 : i < n + w + gs.length
    · obtain ⟨k, rfl⟩ : ∃ k : Fin (toCircuit n w e he).g, i = n + w + k.val :=
        ⟨⟨i - (n + w), by show i - (n + w) < gs.length; omega⟩, by simp; omega⟩
      rw [(toCircuit n w e he).evalAux_gate x wit k]
      have hget : gs[n + w + k.val - (n + w)]? = some gs[k.val] := by
        rw [Nat.add_sub_cancel_left]
        exact List.getElem?_eq_getElem k.isLt
      rw [evalWire_of_some _ _ (Nat.le_add_right _ _) hget]
      obtain ⟨hk1, hk2⟩ := hwf k.val k.isLt
      simp only [hk1, hk2, and_self, ↓reduceIte]
      rw [← ih _ hk1, ← ih _ hk2]
      rfl
    · rw [evalWire_of_none _ _ (by omega) (List.getElem?_eq_none (by omega))]
      have h1' : ¬ i < (toCircuit n w e he).n := h1
      have h2' : ¬ i < (toCircuit n w e he).n + (toCircuit n w e he).w := h2
      have h3' : ¬ i < (toCircuit n w e he).n + (toCircuit n w e he).w +
          (toCircuit n w e he).g := h3
      rw [BoolCircuit.evalAux]
      simp only [h1', h2', h3', ↓reduceDIte]

/-- **The language of the circuit of an expression**: the instances `x` for which some witness
makes the expression true. -/
theorem mem_language_toCircuit (x : Fin n → Bool) :
    x ∈ (toCircuit n w e he).Language ↔ ∃ wit : Fin w → Bool, e.eval (Fin.append x wit) = true := by
  have key : ∀ wit : Fin w → Bool,
      (toCircuit n w e he).evalAux x wit (toCircuit n w e he).outW = e.eval (Fin.append x wit) := by
    intro wit
    rw [evalAux_toCircuit e he x wit, toCircuit_outW, evalWire_compile]
  exact exists_congr fun wit => by rw [key wit]

end BExpr

end LatticePrepro

namespace LatticePrepro

namespace ThreeSAT

variable {v : ℕ}

/-- The witness assignment `a` read off a witness `wit` (the last wire is the dummy). -/
def assignOf (wit : Fin (v + 1) → Bool) : Fin v → Bool := fun i => wit (Fin.castSucc i)

/-- The value of the leaf assignment `Fin.append (encode x) wit` at an input leaf. -/
lemma append_inputLeaf (x : Instance v) (wit : Fin (v + 1) → Bool) (c : Clause v) :
    Fin.append (encode x) wit (inputLeaf c) = x c := by
  simp [inputLeaf, encode]

/-- The value of the leaf assignment `Fin.append (encode x) wit` at a witness leaf. -/
lemma append_varLeaf (x : Instance v) (wit : Fin (v + 1) → Bool) (i : Fin v) :
    Fin.append (encode x) wit (varLeaf i) = assignOf wit i := by
  simp [varLeaf, assignOf]

lemma eval_litExpr (x : Instance v) (wit : Fin (v + 1) → Bool) (l : Fin v × Bool) :
    (litExpr l).eval (Fin.append (encode x) wit) = true ↔ assignOf wit l.1 = l.2 := by
  simp [litExpr, append_varLeaf]

/-- The value of the clause expression: the clause, if present, is satisfied by the witness
assignment. -/
lemma eval_clauseExpr (x : Instance v) (wit : Fin (v + 1) → Bool) (c : Clause v) :
    (clauseExpr c).eval (Fin.append (encode x) wit) = true ↔
      (x c = true → c.Satisfied (assignOf wit)) := by
  simp only [clauseExpr, BExpr.eval_imp, BExpr.eval_or, BExpr.eval_leaf, append_inputLeaf,
    Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, eval_litExpr, Clause.Satisfied]
  constructor
  · rintro (h | h | h | h) hx
    · rw [hx] at h; exact absurd h (by decide)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  · intro h
    by_cases hx : x c = true
    · obtain ⟨j, hj⟩ := h hx
      fin_cases j
      · exact Or.inr (Or.inl hj)
      · exact Or.inr (Or.inr (Or.inl hj))
      · exact Or.inr (Or.inr (Or.inr hj))
    · exact Or.inl (Bool.eq_false_iff.mpr hx)

/-- The value of the verifier expression: every present clause is satisfied by the witness
assignment. -/
lemma eval_formula (x : Instance v) (wit : Fin (v + 1) → Bool) :
    (formula v).eval (Fin.append (encode x) wit) = true ↔
      ∀ c, x c = true → c.Satisfied (assignOf wit) := by
  rw [formula, BExpr.eval_bigAnd, List.all_eq_true]
  simp only [List.mem_map, List.mem_finRange, true_and, forall_exists_index,
    forall_apply_eq_imp_iff, eval_clauseExpr]
  constructor
  · intro h c
    have := h (clauseEquiv v c)
    rwa [Equiv.symm_apply_apply] at this
  · intro h k
    exact h _

/-- **The 3SAT verifier circuit accepts exactly the satisfiable instances.** -/
private theorem mem_language_iff (x : Instance v) : encode x ∈ (circuit v).Language ↔ Satisfiable x := by
  rw [BExpr.mem_language_toCircuit (formula v) (size_formula_pos v) (encode x)]
  simp only [eval_formula, Satisfiable]
  constructor
  · rintro ⟨wit, hwit⟩
    exact ⟨assignOf wit, hwit⟩
  · rintro ⟨a, ha⟩
    refine ⟨Fin.snoc a false, fun c hc => ?_⟩
    have : assignOf (Fin.snoc a false) = a := by
      funext i
      simp [assignOf]
    rw [this]
    exact ha c hc

end ThreeSAT

end LatticePrepro

open LatticePrepro
open LatticePrepro.ThreeSAT
variable {v : ℕ}
theorem solution (x : Instance v) : encode x ∈ (circuit v).Language ↔ Satisfiable x :=
  @LatticePrepro.ThreeSAT.mem_language_iff v x
