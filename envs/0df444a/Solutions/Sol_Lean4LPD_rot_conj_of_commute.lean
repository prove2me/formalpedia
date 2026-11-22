-- Prove2me | solution 1 for Lean4LPD.rot_conj_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:09:54.485545+00:00
-- url     : https://prove2.me/submissions/70b8c147-4956-402a-a7ab-17434ae4be66

module
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Rotation
public import Theorems.Thm_Lean4LPD_rot_mul_rot_neg
public import Theorems.Thm_Lean4LPD_commute_rot

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
variable {A : Type*} [Ring A] [Algebra ℂ A] {G P : A} {θ θ₁ θ₂ : ℝ}
namespace Lean4LPD
theorem _root_.solution (hG : G * G = 1) (h : Commute G P) :
    rot G θ * P * rot G (-θ) = P := by
  rw [(commute_rot h).eq, mul_assoc, rot_mul_rot_neg hG, mul_one]
end Lean4LPD
