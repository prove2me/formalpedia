-- Prove2me | solution 1 for Lean4LPD.rot_mem_unitary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:10:07.508937+00:00
-- url     : https://prove2.me/submissions/0b9af504-6763-4438-a77d-cb1af53b56b4

module
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Rotation
public import Theorems.Thm_Lean4LPD_rot_mul_rot_neg
public import Theorems.Thm_Lean4LPD_rot_neg_mul_rot
public import Theorems.Thm_Lean4LPD_star_rot

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
variable {A : Type*} [Ring A] [Algebra ℂ A] {G P : A} {θ θ₁ θ₂ : ℝ}
variable [StarRing A] [StarModule ℂ A]
namespace Lean4LPD
theorem _root_.solution (hG₂ : G * G = 1) (hG : star G = G) : rot G θ ∈ unitary A :=
  Unitary.mem_iff.2
    ⟨by rw [star_rot hG]; exact rot_neg_mul_rot hG₂,
     by rw [star_rot hG]; exact rot_mul_rot_neg hG₂⟩
end Lean4LPD
