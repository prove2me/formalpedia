-- Prove2me | solution 1 for NaturalProofs.MCircuit.par_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:40:45.278366+00:00
-- url     : https://prove2.me/submissions/0bb02b1d-a5d2-4432-a99f-d08c52f402a8

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
public import Theorems.Thm_NaturalProofs_MCircuit_mapOut_eval
public import Theorems.Thm_NaturalProofs_MCircuit_mapIn_eval
public import Theorems.Thm_NaturalProofs_MCircuit_extend_eval

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
open NaturalProofs.MCircuit
namespace NaturalProofs.MCircuit
theorem _root_.solution [DecidableEq α] (E : α → MCircuit β Unit) (l : List α) (x : β → Bool)
    (b : α) (hb : b ∈ l) : (par E l).eval x b = (E b).eval x () := by
  induction l with
  | nil => simp at hb
  | cons a l ih =>
    simp only [par, mapOut_eval, extend_eval]
    by_cases h : b = a
    · subst h
      simp
    · simp only [h, ite_false, Sum.elim_inr, mapIn_eval]
      exact ih (by simpa [h] using hb)
end NaturalProofs.MCircuit
