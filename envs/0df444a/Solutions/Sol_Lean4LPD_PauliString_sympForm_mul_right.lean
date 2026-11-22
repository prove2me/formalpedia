-- Prove2me | solution 1 for Lean4LPD.PauliString.sympForm_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:02:14.881941+00:00
-- url     : https://prove2.me/submissions/ff77f9a3-8c5e-4282-a90b-ad300b83d93b

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
theorem _root_.solution (u s t : PauliString n) :
    sympForm u (s * t) = sympForm u s + sympForm u t := by
  simp only [sympForm, mul_x, mul_z, dotProduct_add]
  ring
end Lean4LPD.PauliString
