-- Prove2me | solution 1 for Lean4LPD.PauliString.sympForm_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:58:06.467264+00:00
-- url     : https://prove2.me/submissions/c8b4cf44-28b1-4751-8697-1cc1da2c97a6

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
theorem _root_.solution (s : PauliString n) : sympForm s s = 0 := by
  simp only [sympForm]
  rw [dotProduct_comm s.x s.z]
  exact bit_add_self _
end Lean4LPD.PauliString
