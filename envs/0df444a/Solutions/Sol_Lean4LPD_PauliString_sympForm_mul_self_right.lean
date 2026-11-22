-- Prove2me | solution 1 for Lean4LPD.PauliString.sympForm_mul_self_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:02:43.972425+00:00
-- url     : https://prove2.me/submissions/1280b376-c382-41c1-8293-ef5624d9eadb

module
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_mul_right
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_self
attribute [local simp] Lean4LPD.PauliString.sympForm_self

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {s t u : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution (G s : PauliString n) :
    sympForm G (G * s) = sympForm G s := by
  rw [sympForm_mul_right, sympForm_self, zero_add]
end Lean4LPD.PauliString
