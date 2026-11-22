-- Prove2me | solution 1 for Lean4LPD.PauliString.commute_or_anticommute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:08:08.764697+00:00
-- url     : https://prove2.me/submissions/de545195-5b2b-4513-bf42-bc7225a5dab3

module
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Theorems.Thm_Lean4LPD_PauliString_commute_iff_sympForm_eq_zero
public import Theorems.Thm_Lean4LPD_PauliString_anticommute_iff_sympForm_eq_one
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_eq_zero_or_one

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {s t u : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution (s t : PauliString n) :
    Commute s t ∨ s * t = phaseMul 2 (t * s) := by
  rcases sympForm_eq_zero_or_one s t with h | h
  · exact Or.inl ((commute_iff_sympForm_eq_zero s t).2 h)
  · exact Or.inr ((anticommute_iff_sympForm_eq_one s t).2 h)
end Lean4LPD.PauliString
