-- Prove2me | solution 1 for Lean4LPD.star_rot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:09:26.915409+00:00
-- url     : https://prove2.me/submissions/df4f4d6f-5de3-439c-a8e3-5885ff148118

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
variable [StarRing A] [StarModule ℂ A]
namespace Lean4LPD
theorem _root_.solution (hG : star G = G) : star (rot G θ) = rot G (-θ) := by
  simp only [rot, star_add, star_smul, star_one, hG, neg_div, Real.cos_neg, Real.sin_neg,
    Complex.star_def, map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  module
end Lean4LPD
