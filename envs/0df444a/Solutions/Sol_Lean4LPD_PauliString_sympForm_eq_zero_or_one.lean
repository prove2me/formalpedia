-- Prove2me | solution 1 for Lean4LPD.PauliString.sympForm_eq_zero_or_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:58:44.462381+00:00
-- url     : https://prove2.me/submissions/dd7ec01d-5ba4-44af-bf7d-9a238f1a512a

module
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {s t u : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution (s t : PauliString n) :
    sympForm s t = 0 ∨ sympForm s t = 1 :=
  (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) _
end Lean4LPD.PauliString
