-- Prove2me | solution 1 for NaturalProofs.MCircuit.extend_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:38:11.817819+00:00
-- url     : https://prove2.me/submissions/85bf7f55-7df4-4ef5-bcc5-e91fd013f211

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
public import Theorems.Thm_NaturalProofs_evalGates_eq
public import Theorems.Thm_NaturalProofs_evalFrom_append
public import Theorems.Thm_NaturalProofs_length_evalGates
public import Theorems.Thm_NaturalProofs_Wire_local_san
public import Theorems.Thm_NaturalProofs_Wire_eval_san
public import Theorems.Thm_NaturalProofs_Wire_eval_local
public import Theorems.Thm_NaturalProofs_Wire_eval_rw
public import Theorems.Thm_NaturalProofs_Gate_eval_rw
public import Theorems.Thm_NaturalProofs_evalFrom_rw

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
open NaturalProofs.MCircuit
namespace NaturalProofs.MCircuit
theorem _root_.solution (E : MCircuit β α) (C : MCircuit (β ⊕ α) γ) (x : β → Bool) :
    (extend E C).eval x =
      Sum.elim (E.eval x) (C.eval (Sum.elim x (E.eval x))) := by
  set V := evalGates x E.gates with hV
  have hlen : V.length = E.gates.length := length_evalGates x E.gates
  have hσ : ∀ s, (extendσ E s).Local V.length := by
    intro s
    cases s with
    | inl b => trivial
    | inr a => rw [hlen]; exact Wire.local_san _ _
  have hx : (fun s => (extendσ E s).eval x V) = Sum.elim x (E.eval x) := by
    funext s
    cases s with
    | inl b => rfl
    | inr a =>
      simp only [extendσ, Sum.elim_inr]
      rw [← hlen, Wire.eval_san]
      rfl
  have hgates : evalGates x (extend E C).gates = V ++ evalGates (Sum.elim x (E.eval x)) C.gates := by
    have key := evalFrom_rw x V [] _ hσ C.gates
    simp only [List.append_nil] at key
    simp only [extend, evalGates_eq, evalFrom_append]
    rw [← evalGates_eq, ← hV, ← hlen, key, hx]
  funext s
  cases s with
  | inl a =>
    simp only [eval, hgates, Sum.elim_inl]
    simp only [extend, Sum.elim_inl]
    rw [← hlen, Wire.eval_local _ _ _ _ (Wire.local_san _ _), Wire.eval_san]
  | inr c =>
    simp only [eval, hgates, Sum.elim_inr]
    simp only [extend, Sum.elim_inr]
    rw [← hlen, Wire.eval_rw x V _ _ hσ, hx]
end NaturalProofs.MCircuit
