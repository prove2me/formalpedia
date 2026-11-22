-- Prove2me | solution 1 for Lean4LPD.PauliString.sympForm_X1_Z1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:13:15.080797+00:00
-- url     : https://prove2.me/submissions/f6101b1c-ddb3-475b-a25a-3633cdac6e5b

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
theorem _root_.solution : sympForm X1 Z1 = 1 := by decide
end Lean4LPD.PauliString
