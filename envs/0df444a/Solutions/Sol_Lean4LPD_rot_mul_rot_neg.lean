-- Prove2me | solution 1 for Lean4LPD.rot_mul_rot_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:02:25.993411+00:00
-- url     : https://prove2.me/submissions/bfaac23f-a504-43c3-ac50-46147f392078

module
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Rotation

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
variable {A : Type*} [Ring A] [Algebra ℂ A] {G P : A} {θ θ₁ θ₂ : ℝ}
namespace Lean4LPD
theorem _root_.solution (hG : G * G = 1) : rot G θ * rot G (-θ) = 1 := by
  rw [rot_mul_rot hG, add_neg_cancel, rot_zero]
end Lean4LPD
