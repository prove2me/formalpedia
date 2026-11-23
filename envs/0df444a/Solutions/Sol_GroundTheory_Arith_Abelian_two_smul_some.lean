-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.two_smul_some
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:46.910049+00:00
-- url     : https://prove2.me/submissions/b229ce36-9e86-447c-84ff-4aea4ab4ab91

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_NormEDS
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints
import Theorems.Thm_GroundTheory_Arith_Abelian_Psi3_eval
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
theorem _root_.solution {x y : F} (h : W.toAffine.Nonsingular x y) :
    ((2 : ℤ) • Point.some x y h = 0 ↔ 2 * y + W.a₁ * x + W.a₃ = 0) ∧
      (2 * y + W.a₁ * x + W.a₃ ≠ 0 →
        xOf W ((2 : ℤ) • Point.some x y h) * (2 * y + W.a₁ * x + W.a₃) ^ 2 =
          x * (2 * y + W.a₁ * x + W.a₃) ^ 2 - W.Ψ₃.eval x) := by
  have hiff : y = W.toAffine.negY x y ↔ 2 * y + W.a₁ * x + W.a₃ = 0 := by
    rw [negY]; constructor <;> intro h' <;> linear_combination h'
  rw [two_zsmul]
  by_cases hb : 2 * y + W.a₁ * x + W.a₃ = 0
  · exact ⟨iff_of_true (Point.add_self_of_Y_eq (hiff.mpr hb)) hb, fun h' => absurd hb h'⟩
  have hy : y ≠ W.toAffine.negY x y := fun h' => hb (hiff.mp h')
  rw [Point.add_self_of_Y_ne hy]
  refine ⟨iff_of_false (Point.some_ne_zero _) hb, fun _ => ?_⟩
  simp only [xOf_some]
  have hl : W.toAffine.slope x x y y * (y - (-y - W.a₁ * x - W.a₃)) =
      3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    rw [slope_of_Y_ne rfl hy, negY, div_mul_cancel₀]
    rw [show y - (-y - W.a₁ * x - W.a₃) = 2 * y + W.a₁ * x + W.a₃ by ring]; exact hb
  set l := W.toAffine.slope x x y y
  have e := (equation_iff _ _).mp h.1
  refine eq_of_mul_sub_eq_zero (M := (2 * y + W.a₁ * x + W.a₃) ^ 2) (pow_ne_zero _ hb) ?_
  rw [Psi3_eval]
  simp only [addX, b₂, b₄, b₆, b₈]
  linear_combination ((W.a₁ * x + W.a₃ + 2 * y) ^ 2 * (l * W.a₁ * x + l * W.a₃ + 2 * l * y +
      W.a₁ ^ 2 * x + W.a₁ * W.a₃ + W.a₁ * y + 2 * W.a₂ * x + W.a₄ + 3 * x ^ 2)) * hl +
    (-(W.a₁ ^ 2 + 4 * W.a₂ + 12 * x) * (W.a₁ * x + W.a₃ + 2 * y) ^ 2) * e
end GroundTheory.Arith.Abelian
