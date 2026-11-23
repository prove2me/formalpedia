-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.xOf_add_add_xOf_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:31.708193+00:00
-- url     : https://prove2.me/submissions/8e37adb7-aa2f-4094-954c-6b8ecddf7c83

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_NormEDS
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
section
namespace GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
private theorem eq_of_mul_sub_eq_zero {R : Type*} [CommRing R] [IsDomain R] {M x y : R}
    (hM : M ≠ 0) (h : M * (x - y) = 0) : x = y :=
  sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hM)
section Sequence
variable {R : Type*} [CommRing R] [IsDomain R]
end Sequence
section Values
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
end Values
section Algebra
variable {F : Type*} [Field F]
end Algebra
section Points
variable {F : Type*} [Field F] (W : WeierstrassCurve F)
variable [DecidableEq F]
end Points
section Main
variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
  {x₀ y₀ : F} (h₀ : W.toAffine.Nonsingular x₀ y₀)
end Main
section Statements
variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
  {x₀ y₀ : F} (h₀ : W.toAffine.Nonsingular x₀ y₀)
end Statements
end GroundTheory.Arith.Abelian
end

set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
variable {F : Type*} [Field F] (W : WeierstrassCurve F)
variable [DecidableEq F]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {x₁ y₁ x₂ y₂ : F} (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) (hx : x₁ ≠ x₂) :
    Point.some x₁ y₁ h₁ + .some x₂ y₂ h₂ ≠ 0 ∧ Point.some x₁ y₁ h₁ - .some x₂ y₂ h₂ ≠ 0 ∧
      (xOf W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) + xOf W (.some x₁ y₁ h₁ - .some x₂ y₂ h₂)) *
          (x₁ - x₂) ^ 2 =
        2 * x₁ * x₂ * (x₁ + x₂) + W.b₂ * x₁ * x₂ + W.b₄ * (x₁ + x₂) + W.b₆ := by
  have hs : Point.some x₁ y₁ h₁ - .some x₂ y₂ h₂ =
      .some x₁ y₁ h₁ + .some x₂ (W.toAffine.negY x₂ y₂) ((nonsingular_neg ..).mpr h₂) := by
    rw [sub_eq_add_neg, Point.neg_some]
  rw [hs, Point.add_of_X_ne hx, Point.add_of_X_ne hx]
  refine ⟨Point.some_ne_zero _, Point.some_ne_zero _, ?_⟩
  simp only [xOf_some]
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have hl : W.toAffine.slope x₁ x₂ y₁ y₂ * (x₁ - x₂) = y₁ - y₂ := by
    rw [slope_of_X_ne hx, div_mul_cancel₀ _ hd]
  have hlp : W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂) * (x₁ - x₂) =
      y₁ - (-y₂ - W.a₁ * x₂ - W.a₃) := by
    rw [slope_of_X_ne hx, div_mul_cancel₀ _ hd, negY]
  set l := W.toAffine.slope x₁ x₂ y₁ y₂
  set lp := W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)
  have e1 := (equation_iff _ _).mp h₁.1
  have e2 := (equation_iff _ _).mp h₂.1
  refine eq_of_mul_sub_eq_zero (M := (x₁ - x₂) ^ 4) (pow_ne_zero _ hd) ?_
  simp only [addX, b₂, b₄, b₆]
  linear_combination ((x₁ - x₂) ^ 4 * (W.a₁ * x₁ - W.a₁ * x₂ + l * x₁ - l * x₂ + y₁ - y₂)) * hl +
    ((x₁ - x₂) ^ 4 * (W.a₁ * x₁ + W.a₃ + lp * x₁ - lp * x₂ + y₁ + y₂)) * hlp +
    (2 * (x₁ - x₂) ^ 4) * e1 + (2 * (x₁ - x₂) ^ 4) * e2
end GroundTheory.Arith.Abelian
