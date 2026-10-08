-- Prove2me | solution 1 for MazurTransfer.order49_no_rational_affine_point
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T05:57:10.8647+00:00
-- url     : https://prove2.me/submissions/89c743d8-bfda-4fe5-8396-e0ce517f2a89

import Definitions.Def_MazurTransfer_Order49BacktrackingCofactors
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49HauptmodulJNumerator
import Definitions.Def_MazurTransfer_Order49MarkedOriginPoint
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
import Definitions.Def_MazurTransfer_OrderFortyNinePlaneTransferData
import Mathlib
import Theorems.Thm_MazurTransfer_order49_all_bounded_resultants_nonzero
import Theorems.Thm_MazurTransfer_order49_geometry_orderSevenQuotient_isElliptic
import Theorems.Thm_MazurTransfer_order49_marked_origin_orderSevenFamily_parameters_ne
import Theorems.Thm_MazurTransfer_order49_point_map_orderSevenPointMap_some_eq_zero_iff
import Theorems.Thm_MazurTransfer_order49_residual_orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_bounded_resultants
import Theorems.Thm_MazurTransfer_order49_residual_orderSevenResidualHauptmodul_spec_of_order_fortyNine_of_kernel
import Theorems.Thm_MazurTransfer_x0_49_plane_has_no_noncuspidal_point
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
open Polynomial
open _root_.WeierstrassCurve
open _root_.WeierstrassCurve.Affine
open _root_.WeierstrassCurve.Affine.Point hiding neg_zero map_zero
theorem MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.bounded_resultants_ne_zero (d : ℚ) (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hcubic : d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0) :
    resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d) 33 7 ≠ 0 ∧
      resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d) 33 7 ≠ 0 ∧
      resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2 d) 33 7 ≠ 0 := by
  exact MazurTransfer.order49_all_bounded_resultants_nonzero d hd0 hd1 hcubic
theorem MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.MazurTorsion.Kubert.orderSevenFamily_parameters_ne (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    d ≠ 0 ∧ d ≠ 1 ∧
      d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0 := by
  apply MazurTransfer.order49_marked_origin_orderSevenFamily_parameters_ne <;> assumption
theorem MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.MazurTorsion.Kubert.orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_bounded_resultants {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hQ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d
      ((7 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP) = 0)
    (hres0 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d) 33 7 ≠ 0)
    (hres1 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d) 33 7 ≠ 0)
    (hres2 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2 d) 33 7 ≠ 0) :
    MazurTorsion.Kubert.orderSevenG7F (MazurTorsion.Kubert.orderSevenFrickeParameter d)
        (MazurTorsion.Kubert.orderSevenResidualHauptmodul d x y) = 0 := by
  exact MazurTransfer.order49_residual_orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_bounded_resultants (d := d) (x := x) (y := y) hP hQ hkernel hres0 hres1 hres2
theorem MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.MazurTorsion.Kubert.orderSevenPointMap_some_eq_zero_iff {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y) :
    MazurTorsion.Kubert.orderSevenPointMap d (.some x y hP) = 0 ↔
      MazurTorsion.Kubert.OrderSevenKernelX d x := by
  apply MazurTransfer.order49_point_map_orderSevenPointMap_some_eq_zero_iff <;> assumption
theorem MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.MazurTorsion.Kubert.orderSevenQuotient_isElliptic (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    (MazurTorsion.Kubert.orderSevenQuotient d).IsElliptic := by
  apply MazurTransfer.order49_geometry_orderSevenQuotient_isElliptic <;> assumption
theorem MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.MazurTorsion.Kubert.orderSevenResidualHauptmodul_spec_of_order_fortyNine_of_kernel {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hQ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d
      ((7 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP) = 0) :
    MazurTorsion.Kubert.orderSevenResidualHauptmodul d x y ≠ 0 ∧
      MazurTorsion.Kubert.orderSevenJNumerator (MazurTorsion.Kubert.orderSevenResidualHauptmodul d x y) *
          (MazurTorsion.Kubert.orderSevenQuotient d).Δ =
        (MazurTorsion.Kubert.orderSevenQuotient d).c₄ ^ 3 *
          MazurTorsion.Kubert.orderSevenResidualHauptmodul d x y ^ 7 := by
  apply MazurTransfer.order49_residual_orderSevenResidualHauptmodul_spec_of_order_fortyNine_of_kernel <;> assumption
theorem MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.MazurTorsion.XZeroFortyNine.no_noncuspidal_correspondence_point {s B : ℚ} (hs : s ≠ 0) (hB : B ≠ 0)
    (hG : MazurTorsion.Kubert.orderSevenG7F s B = 0) :
    False := by
  exact MazurTransfer.x0_49_plane_has_no_noncuspidal_point s B hs hB hG
namespace MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone
/-
Copyright (c) 2026 Kevin Buzzard, Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude, Vasily Ilin
-/




section

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (C : VariableChange F)



lemma variableChange_negY (x y : F) :
    W.toAffine.negY ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      = (C.u : F) ^ 3 * (C • W).toAffine.negY x y + (C.u : F) ^ 2 * C.s * x + C.t := by
  simp [negY, variableChange_a₁, variableChange_a₃]
  field

/-- The image of a pair of points under the change of variables satisfies the `y₁ = -y₂`
degeneracy condition only if the original pair does. -/
lemma variableChange_negY_ne {x₁ x₂ y₁ y₂ : F}
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    ¬((C.u : F) ^ 2 * x₁ + C.r = (C.u : F) ^ 2 * x₂ + C.r ∧
      (C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t = W.toAffine.negY
        ((C.u : F) ^ 2 * x₂ + C.r) ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t)) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  intro ⟨hX, hY⟩
  have hx : x₁ = x₂ := mul_left_cancel₀ (pow_ne_zero 2 hu) (by linear_combination hX)
  subst hx
  rw [MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.variableChange_negY] at hY
  exact hxy ⟨rfl, mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination hY)⟩

lemma variableChange_addX (x₁ x₂ ℓ : F) :
    W.toAffine.addX ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r) ((C.u : F) * ℓ + C.s)
      = (C.u : F) ^ 2 * (C • W).toAffine.addX x₁ x₂ ℓ + C.r := by
  simp [addX, variableChange_a₁, variableChange_a₂]
  field

lemma variableChange_negAddY (x₁ x₂ y₁ ℓ : F) :
    W.toAffine.negAddY ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) ((C.u : F) * ℓ + C.s)
      = (C.u : F) ^ 3 * (C • W).toAffine.negAddY x₁ x₂ y₁ ℓ
        + (C.u : F) ^ 2 * C.s * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
  simp [negAddY, addX, variableChange_a₁, variableChange_a₂]
  field

lemma variableChange_addY (x₁ x₂ y₁ ℓ : F) :
    W.toAffine.addY ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) ((C.u : F) * ℓ + C.s)
      = (C.u : F) ^ 3 * (C • W).toAffine.addY x₁ x₂ y₁ ℓ
        + (C.u : F) ^ 2 * C.s * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
  simp only [addY, MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.variableChange_negAddY, MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.variableChange_addX, MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.variableChange_negY]

lemma variableChange_slope [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
    (h₁ : (C • W).toAffine.Equation x₁ y₁) (h₂ : (C • W).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    W.toAffine.slope ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t)
        ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t)
      = (C.u : F) * (C • W).toAffine.slope x₁ x₂ y₁ y₂ + C.s := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rcases eq_or_ne x₁ x₂ with rfl | hx
  · have hy : y₁ ≠ (C • W).toAffine.negY x₁ y₂ := fun h ↦ hxy ⟨rfl, h⟩
    obtain rfl := Y_eq_of_Y_ne h₁ h₂ rfl hy
    have hΦy : (C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t
        ≠ W.toAffine.negY ((C.u : F) ^ 2 * x₁ + C.r)
            ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) := by
      rw [MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.variableChange_negY]
      exact fun h ↦ hy (mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination h))
    rw [W.toAffine.slope_of_Y_ne rfl hΦy, (C • W).toAffine.slope_of_Y_ne rfl hy,
      ← mul_div_assoc, div_add' _ _ _ (sub_ne_zero.mpr hy),
      div_eq_div_iff (sub_ne_zero.mpr hΦy) (sub_ne_zero.mpr hy)]
    simp [negY, variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄]
    field
  · have hΦx : (C.u : F) ^ 2 * x₁ + C.r ≠ (C.u : F) ^ 2 * x₂ + C.r := by
      simpa [mul_right_inj' (pow_ne_zero 2 hu)] using hx
    rw [W.toAffine.slope_of_X_ne hΦx, (C • W).toAffine.slope_of_X_ne hx]
    have h1 := sub_ne_zero.mpr hΦx
    have h2 := sub_ne_zero.mpr hx
    field

/-- A point `(x, y)` lies on `C • W` if and only if `(u²x + r, u³y + u²sx + t)` lies on `W`. -/
lemma variableChange_equation (x y : F) :
    W.toAffine.Equation ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      ↔ (C • W).toAffine.Equation x y := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  simp only [equation_iff', variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, Units.val_inv_eq_inv_val, field]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> linear_combination h

/-- The `Y`-derivative of a Weierstrass equation under an admissible change of variables.
This formula does not require either equation to be elliptic. -/
lemma variableChange_polynomialY (x y : F) :
    W.toAffine.polynomialY.evalEval ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) =
      (C.u : F) ^ 3 * (C • W).toAffine.polynomialY.evalEval x y := by
  simp only [Affine.evalEval_polynomialY, variableChange_a₁, variableChange_a₃,
    Units.val_inv_eq_inv_val]
  field

/-- The `X`-derivative of a Weierstrass equation under an admissible change of variables.
The correction term is the chain-rule contribution from the `sx` term in the new `Y` coordinate.
This formula does not require either equation to be elliptic. -/
lemma variableChange_polynomialX (x y : F) :
    W.toAffine.polynomialX.evalEval ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) =
      (C.u : F) ^ 4 * (C • W).toAffine.polynomialX.evalEval x y -
        C.s * ((C.u : F) ^ 3 * (C • W).toAffine.polynomialY.evalEval x y) := by
  simp only [Affine.evalEval_polynomialX, Affine.evalEval_polynomialY, variableChange_a₁,
    variableChange_a₂, variableChange_a₃, variableChange_a₄,
    Units.val_inv_eq_inv_val]
  field

/-- An admissible change of variables identifies the nonsingular loci even when the common
Weierstrass cubic is singular. -/
lemma variableChange_nonsingular (x y : F) :
    W.toAffine.Nonsingular ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) ↔
      (C • W).toAffine.Nonsingular x y := by
  rw [Affine.Nonsingular, Affine.Nonsingular, MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.variableChange_equation W C,
    MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.variableChange_polynomialX W C, MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.variableChange_polynomialY W C]
  apply and_congr_right
  intro _
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  constructor
  · rintro (hx | hy)
    · by_cases hY : (C • W).toAffine.polynomialY.evalEval x y = 0
      · left
        intro hX
        apply hx
        rw [hY, mul_zero, mul_zero, sub_zero, hX, mul_zero]
      · exact Or.inr hY
    · exact Or.inr fun hY ↦ hy (mul_eq_zero.mpr <| Or.inr hY)
  · rintro (hx | hy)
    · by_cases hY : (C • W).toAffine.polynomialY.evalEval x y = 0
      · left
        rw [hY, mul_zero, mul_zero, sub_zero]
        exact mul_ne_zero (pow_ne_zero 4 hu) hx
      · exact Or.inr (mul_ne_zero (pow_ne_zero 3 hu) hY)
    · exact Or.inr (mul_ne_zero (pow_ne_zero 3 hu) hy)



namespace Point

/-- The underlying point map of the change of variables, sending `0` to `0`. -/
def mapVariableChangeFun : (C • W).toAffine.Point → W.toAffine.Point
  | .zero => .zero
  | .some x y h => .some ((C.u : F) ^ 2 * x + C.r)
      ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      ((MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.variableChange_nonsingular W C x y).mpr h)

@[simp] lemma mapVariableChangeFun_zero : MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.mapVariableChangeFun W C 0 = 0 := rfl

lemma mapVariableChangeFun_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.mapVariableChangeFun W C (.some x y h)
      = .some ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
          ((MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.variableChange_nonsingular W C x y).mpr h) := rfl

lemma some_eq_some (W : WeierstrassCurve F) {x₁ x₂ y₁ y₂ : F} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : W.toAffine.Nonsingular x₁ y₁} {h₂ : W.toAffine.Nonsingular x₂ y₂} :
    (some x₁ y₁ h₁ : W.toAffine.Point) = some x₂ y₂ h₂ := by
  subst hx hy
  rfl

lemma mapVariableChangeFun_injective :
    Function.Injective (MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.mapVariableChangeFun W C) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · simp [MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.mapVariableChangeFun] at h
  · simp [MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.mapVariableChangeFun] at h
  · rw [MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.mapVariableChangeFun_some, MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.mapVariableChangeFun_some] at h
    injection h with hX hY
    have hx : x₁ = x₂ := mul_left_cancel₀ (pow_ne_zero 2 hu) (by linear_combination hX)
    exact MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.some_eq_some (C • W) hx
      (mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination hY - (C.u : F) ^ 2 * C.s * hx))

variable [DecidableEq F]

/-- Transport of the affine point group along an equality of Weierstrass curves. -/
def equivOfEq {V V' : WeierstrassCurve F} (h : V = V') :
    V.toAffine.Point ≃+ V'.toAffine.Point := by
  subst h
  exact AddEquiv.refl _

@[simp] lemma equivOfEq_some {V V' : WeierstrassCurve F} (h : V = V') {x y : F}
    (hns : V.toAffine.Nonsingular x y) :
    MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.equivOfEq h (some x y hns) = some x y (h ▸ hns) := by
  subst h
  rfl

/-- The group homomorphism induced by the admissible change of variables. -/
def mapVariableChange : (C • W).toAffine.Point →+ W.toAffine.Point where
  toFun := MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.mapVariableChangeFun W C
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    simp only [MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.mapVariableChangeFun_some]
    have e₁ : (C • W).toAffine.Equation x₁ y₁ := h₁.left
    have e₂ : (C • W).toAffine.Equation x₂ y₂ := h₂.left
    by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
    · rw [add_of_Y_eq hxy.1 hxy.2, MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.mapVariableChangeFun_zero]
      refine (add_of_Y_eq ?_ ?_).symm
      · rw [hxy.1]
      · rw [MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.variableChange_negY, hxy.2, hxy.1]
    · rw [add_some hxy, MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.mapVariableChangeFun_some, add_some (MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.variableChange_negY_ne W C hxy)]
      simp only [MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.variableChange_slope W C e₁ e₂ hxy, MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.variableChange_addX, MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.variableChange_addY]

/-- The point-group isomorphism induced by the admissible change of variables. -/
def equivVariableChange : (C • W).toAffine.Point ≃+ W.toAffine.Point :=
  have hright : ∀ P, MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.mapVariableChangeFun W C
      (MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.mapVariableChangeFun (C • W) C⁻¹ (MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.equivOfEq (inv_smul_smul C W).symm P)) = P := by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    rintro (_ | ⟨X, Y, h⟩)
    · simp [← zero_def]
    · rw [MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.equivOfEq_some, MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.mapVariableChangeFun_some, MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.mapVariableChangeFun_some]
      refine MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.some_eq_some W ?_ ?_ <;>
        (simp only [VariableChange.inv_def, Units.val_inv_eq_inv_val]; field)
  { toFun := MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.mapVariableChangeFun W C
    invFun := fun P ↦ MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.mapVariableChangeFun (C • W) C⁻¹ (MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.equivOfEq (inv_smul_smul C W).symm P)
    left_inv := Function.RightInverse.leftInverse_of_injective hright
      (MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.mapVariableChangeFun_injective W C)
    right_inv := hright
    map_add' := (MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.mapVariableChange W C).map_add' }

lemma equivVariableChange_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.equivVariableChange W C (.some x y h)
      = .some ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
          ((MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.variableChange_nonsingular W C x y).mpr h) := rfl

end Point

end WeierstrassCurve.Affine

end

end MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone

namespace MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/




open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert
















































































/-- The Fricke/backtracking Hauptmodul is nonzero on every nonsingular
member of the source family. -/
theorem orderSevenFrickeParameter_ne_zero
    (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    MazurTorsion.Kubert.orderSevenFrickeParameter d ≠ 0 := by
  obtain ⟨hd0, hd1, hK⟩ := MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.MazurTorsion.Kubert.orderSevenFamily_parameters_ne d
  exact div_ne_zero hK
    (mul_ne_zero hd0 (sub_ne_zero.mpr hd1))























@[simp]
theorem orderSevenPointMap_origin
    (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    MazurTorsion.Kubert.orderSevenPointMap d (MazurTorsion.Kubert.orderSevenOrigin d) = 0 := by
  apply (MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.MazurTorsion.Kubert.orderSevenPointMap_some_eq_zero_iff
    (MazurTorsion.Kubert.orderSevenOrigin_nonsingular d)).mpr
  exact Or.inl rfl



























end MazurTorsion.Kubert

end MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone

namespace MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



section
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert























/-- If the tangent at the origin has triple contact, then the origin is killed by three.
This is the small group-law fact used during Tate normalization. -/
lemma three_nsmul_origin_eq_zero
    (W : WeierstrassCurve ℚ) (ha₂ : W.a₂ = 0) (ha₄ : W.a₄ = 0)
    (ha₃ : W.a₃ ≠ 0) (h00 : W.toAffine.Nonsingular 0 0) :
    WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 = 0 := by
  have hvertical : (0 : ℚ) ≠ W.toAffine.negY 0 0 := by
    simp only [WeierstrassCurve.Affine.negY]
    intro h
    apply ha₃
    linarith
  have hslope : W.toAffine.slope 0 0 0 0 = 0 := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hvertical]
    simp only [WeierstrassCurve.Affine.negY, ha₂, ha₄]
    ring_nf
  have hdouble :
      WeierstrassCurve.Affine.Point.some 0 0 h00 +
          WeierstrassCurve.Affine.Point.some 0 0 h00 =
        -WeierstrassCurve.Affine.Point.some 0 0 h00 := by
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne' hvertical]
    congr 1
    refine MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.some_eq_some W ?_ ?_
    · simp only [WeierstrassCurve.Affine.addX, hslope, ha₂]
      ring
    · simp only [WeierstrassCurve.Affine.negAddY,
        WeierstrassCurve.Affine.addX, hslope, ha₂]
      ring
  rw [hdouble, neg_add_cancel]

/-- Tate normalization retaining the discriminant and `c₄` scaling
parameters. -/
theorem exists_tateNormalCurve_scaled
    (W : WeierstrassCurve ℚ)
    (P : W.toAffine.Point) (hP2 : P + P ≠ 0) (hP3 : P + P + P ≠ 0) :
    ∃ (b c u : ℚ) (_ : u ≠ 0) (_ : b ≠ 0)
      (h00 : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular 0 0)
      (e : W.toAffine.Point ≃+ (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Point),
      e P = WeierstrassCurve.Affine.Point.some 0 0 h00 ∧
        u ^ 12 * W.Δ = (MazurTorsion.Kubert.tateNormalCurve b c).Δ ∧
        u ^ 4 * W.c₄ = (MazurTorsion.Kubert.tateNormalCurve b c).c₄ ∧
        u ^ 6 * W.c₆ = (MazurTorsion.Kubert.tateNormalCurve b c).c₆ := by
  obtain ⟨X, Y, hns, hPxy⟩ :
      ∃ (X Y : ℚ) (h : W.toAffine.Nonsingular X Y),
        P = WeierstrassCurve.Affine.Point.some X Y h := by
    rcases hcase : P with _ | ⟨X, Y, h⟩
    · exfalso
      apply hP2
      rw [hcase]
      simp [← WeierstrassCurve.Affine.Point.zero_def]
    · exact ⟨X, Y, h, rfl⟩
  have hnotvertical : Y ≠ W.toAffine.negY X Y := fun h =>
    hP2 (by
      rw [hPxy]
      exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq h)
  have htangentDenom : W.a₃ + X * W.a₁ + 2 * Y ≠ 0 := by
    intro h
    apply hnotvertical
    rw [WeierstrassCurve.Affine.negY]
    linarith
  set s : ℚ :=
    (W.a₄ + 2 * X * W.a₂ - Y * W.a₁ + 3 * X ^ 2) /
      (W.a₃ + X * W.a₁ + 2 * Y) with hs
  set C₁ : WeierstrassCurve.VariableChange ℚ := ⟨1, X, s, Y⟩ with hC₁
  have hC₁a₃ : (C₁ • W).a₃ = W.a₃ + X * W.a₁ + 2 * Y := by
    rw [WeierstrassCurve.variableChange_a₃, hC₁]
    simp
  have hC₁a₄ : (C₁ • W).a₄ = 0 := by
    rw [WeierstrassCurve.variableChange_a₄, hC₁]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    rw [hs]
    field_simp
    ring
  have hC₁a₆ : (C₁ • W).a₆ = 0 := by
    have heq := hns.1
    rw [WeierstrassCurve.Affine.equation_iff] at heq
    rw [WeierstrassCurve.variableChange_a₆, hC₁]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    linear_combination -heq
  have h00₁ : (C₁ • W).toAffine.Nonsingular 0 0 :=
    WeierstrassCurve.Affine.nonsingular_zero.mpr
      ⟨hC₁a₆, Or.inl (by rw [hC₁a₃]; exact htangentDenom)⟩
  have hmap₁ :
      MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.equivVariableChange W C₁
          (WeierstrassCurve.Affine.Point.some 0 0 h00₁) = P := by
    rw [MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.equivVariableChange_some, hPxy]
    exact MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.some_eq_some W
      (by simp [hC₁]) (by simp [hC₁])
  have hC₁a₂ : (C₁ • W).a₂ ≠ 0 := by
    intro hzero
    apply hP3
    have htriple :
        WeierstrassCurve.Affine.Point.some 0 0 h00₁ +
            WeierstrassCurve.Affine.Point.some 0 0 h00₁ +
            WeierstrassCurve.Affine.Point.some 0 0 h00₁ = 0 :=
      MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.MazurTorsion.Kubert.three_nsmul_origin_eq_zero (C₁ • W) hzero hC₁a₄
        (by rw [hC₁a₃]; exact htangentDenom) h00₁
    have himage :=
      congrArg (MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.equivVariableChange W C₁) htriple
    rwa [map_add, map_add, map_zero, hmap₁] at himage
  set scale : ℚˣ :=
    Units.mk0 ((C₁ • W).a₃ / (C₁ • W).a₂)
      (div_ne_zero (by rw [hC₁a₃]; exact htangentDenom) hC₁a₂)
  set C₂ : WeierstrassCurve.VariableChange ℚ := ⟨scale, 0, 0, 0⟩ with hC₂
  have hscale : (scale : ℚ) = (C₁ • W).a₃ / (C₁ • W).a₂ := rfl
  have hscale0 : (scale : ℚ) ≠ 0 := scale.ne_zero
  set b : ℚ := -(C₂ • (C₁ • W)).a₂ with hb
  set c : ℚ := 1 - (C₂ • (C₁ • W)).a₁ with hc
  have hC₂a₄ : (C₂ • (C₁ • W)).a₄ = 0 := by
    rw [WeierstrassCurve.variableChange_a₄, hC₂]
    simp [hC₁a₄]
  have hC₂a₆ : (C₂ • (C₁ • W)).a₆ = 0 := by
    rw [WeierstrassCurve.variableChange_a₆, hC₂]
    simp [hC₁a₆]
  have hC₂a₂a₃ : (C₂ • (C₁ • W)).a₃ = (C₂ • (C₁ • W)).a₂ := by
    rw [WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.variableChange_a₂, hC₂]
    simp only [Units.val_inv_eq_inv_val]
    field_simp [hscale]
    rw [hscale]
    field_simp
    ring
  have hC₂a₂ :
      (C₂ • (C₁ • W)).a₂ = ((scale : ℚ))⁻¹ ^ 2 * (C₁ • W).a₂ := by
    rw [WeierstrassCurve.variableChange_a₂, hC₂]
    simp
  have hC₂a₂ne : (C₂ • (C₁ • W)).a₂ ≠ 0 := by
    rw [hC₂a₂]
    exact mul_ne_zero (pow_ne_zero 2 (inv_ne_zero hscale0)) hC₁a₂
  have hb0 : b ≠ 0 := by
    rw [hb, neg_ne_zero]
    exact hC₂a₂ne
  have hcurve :
      C₂ • (C₁ • W) = MazurTorsion.Kubert.tateNormalCurve b c := by
    ext <;> simp [MazurTorsion.Kubert.tateNormalCurve, hb, hc, hC₂a₄, hC₂a₆, hC₂a₂a₃]
  have h00₂ : (C₂ • (C₁ • W)).toAffine.Nonsingular 0 0 :=
    WeierstrassCurve.Affine.nonsingular_zero.mpr
      ⟨hC₂a₆, Or.inl (by rw [hC₂a₂a₃]; exact hC₂a₂ne)⟩
  have hdisc :
      ((scale : ℚ))⁻¹ ^ 12 * W.Δ = (C₂ • (C₁ • W)).Δ := by
    rw [WeierstrassCurve.variableChange_Δ,
      WeierstrassCurve.variableChange_Δ, hC₁, hC₂]
    simp
  refine ⟨b, c, ((scale : ℚ))⁻¹, inv_ne_zero hscale0, hb0,
    hcurve ▸ h00₂,
    (MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm.trans
      ((MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.equivVariableChange (C₁ • W) C₂).symm.trans
        (MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.equivOfEq hcurve)), ?_, ?_, ?_, ?_⟩
  · have hfirst :
        (MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm P =
          WeierstrassCurve.Affine.Point.some 0 0 h00₁ := by
      rw [← hmap₁]
      exact (MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm_apply_apply _
    have hsecond :
        MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.equivVariableChange (C₁ • W) C₂
            (WeierstrassCurve.Affine.Point.some 0 0 h00₂) =
          WeierstrassCurve.Affine.Point.some 0 0 h00₁ := by
      rw [MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.equivVariableChange_some]
      exact MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.some_eq_some _
        (by simp [hC₂]) (by simp [hC₂])
    simp only [AddEquiv.trans_apply, hfirst, ← hsecond,
      AddEquiv.symm_apply_apply, MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.equivOfEq_some]
  · rw [hdisc, hcurve]
  · have hc₄ :
        ((scale : ℚ))⁻¹ ^ 4 * W.c₄ = (C₂ • (C₁ • W)).c₄ := by
      rw [WeierstrassCurve.variableChange_c₄,
        WeierstrassCurve.variableChange_c₄, hC₁, hC₂]
      simp
    rw [hc₄, hcurve]
  · have hc₆ :
        ((scale : ℚ))⁻¹ ^ 6 * W.c₆ = (C₂ • (C₁ • W)).c₆ := by
      rw [WeierstrassCurve.variableChange_c₆,
        WeierstrassCurve.variableChange_c₆, hC₁, hC₂]
      simp
    rw [hc₆, hcurve]

/-- The marked point `P = (0,0)` doubles to `(b,bc)` on Tate normal form. -/
theorem two_mul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₂ : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular b (b * c),
      WeierstrassCurve.Affine.Point.some 0 0 h00 +
          WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some b (b * c) h₂ := by
  let W := MazurTorsion.Kubert.tateNormalCurve b c
  have hneg : W.toAffine.negY 0 0 = b := by
    simp [W, MazurTorsion.Kubert.tateNormalCurve, WeierstrassCurve.Affine.negY]
  have hnotvertical : (0 : ℚ) ≠ W.toAffine.negY 0 0 := by
    rw [hneg]
    exact fun h => hb h.symm
  have hslope : W.toAffine.slope 0 0 0 0 = 0 := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hnotvertical]
    simp [W, MazurTorsion.Kubert.tateNormalCurve]
  have hx :
      W.toAffine.addX 0 0 (W.toAffine.slope 0 0 0 0) = b := by
    rw [hslope]
    simp [W, MazurTorsion.Kubert.tateNormalCurve]
  have hy :
      W.toAffine.addY 0 0 0 (W.toAffine.slope 0 0 0 0) = b * c := by
    rw [hslope]
    simp [W, MazurTorsion.Kubert.tateNormalCurve, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negY]
    ring
  have h₂ : W.toAffine.Nonsingular b (b * c) := by
    have h :=
      WeierstrassCurve.Affine.nonsingular_add h00 h00
        (fun hxy => hnotvertical hxy.right)
    rwa [hx, hy] at h
  refine ⟨h₂, ?_⟩
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hnotvertical]
  exact MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.some_eq_some W hx hy

/-- The marked point `P = (0,0)` triples to `(c,b-c)` on Tate normal form. -/
theorem three_mul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₃ : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular c (b - c),
      WeierstrassCurve.Affine.Point.some 0 0 h00 +
            WeierstrassCurve.Affine.Point.some 0 0 h00 +
          WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some c (b - c) h₃ := by
  let W := MazurTorsion.Kubert.tateNormalCurve b c
  obtain ⟨h₂, hdouble⟩ := MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.MazurTorsion.Kubert.two_mul_origin_coordinates b c hb h00
  have hslope : W.toAffine.slope b 0 (b * c) 0 = c := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hb]
    field_simp
    ring
  have hx :
      W.toAffine.addX b 0 (W.toAffine.slope b 0 (b * c) 0) = c := by
    rw [hslope]
    simp [W, MazurTorsion.Kubert.tateNormalCurve]
    ring
  have hy :
      W.toAffine.addY b 0 (b * c) (W.toAffine.slope b 0 (b * c) 0) =
        b - c := by
    rw [hslope]
    simp [W, MazurTorsion.Kubert.tateNormalCurve, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negY]
    ring
  have h₃ : W.toAffine.Nonsingular c (b - c) := by
    have h :=
      WeierstrassCurve.Affine.nonsingular_add h₂ h00
        (fun hxy => hb hxy.left)
    rwa [hx, hy] at h
  refine ⟨h₃, ?_⟩
  rw [hdouble]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hb]
  exact MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.some_eq_some W hx hy



/-- In scalar-multiplication notation, `3P = (c,b-c)` for the marked Tate point. -/
theorem three_nsmul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₃ : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular c (b - c),
      (3 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some c (b - c) h₃ := by
  obtain ⟨h₃, htriple⟩ := MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.MazurTorsion.Kubert.three_mul_origin_coordinates b c hb h00
  refine ⟨h₃, ?_⟩
  rw [show (3 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
      WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 by abel]
  exact htriple

/-- If also `c ≠ 0`, then `4P` has the displayed rational coordinates. -/
theorem four_mul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0)
    (h00 : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₄ : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular
        (b * (b - c) / c ^ 2) (b ^ 2 * (c ^ 2 + c - b) / c ^ 3),
      WeierstrassCurve.Affine.Point.some 0 0 h00 +
              WeierstrassCurve.Affine.Point.some 0 0 h00 +
            WeierstrassCurve.Affine.Point.some 0 0 h00 +
          WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some
          (b * (b - c) / c ^ 2) (b ^ 2 * (c ^ 2 + c - b) / c ^ 3) h₄ := by
  let W := MazurTorsion.Kubert.tateNormalCurve b c
  obtain ⟨h₃, htriple⟩ := MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.MazurTorsion.Kubert.three_mul_origin_coordinates b c hb h00
  have hslope : W.toAffine.slope c 0 (b - c) 0 = (b - c) / c := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hc]
    ring
  have hx :
      W.toAffine.addX c 0 (W.toAffine.slope c 0 (b - c) 0) =
        b * (b - c) / c ^ 2 := by
    rw [hslope]
    simp [W, MazurTorsion.Kubert.tateNormalCurve]
    field_simp [hc]
    ring
  have hy :
      W.toAffine.addY c 0 (b - c) (W.toAffine.slope c 0 (b - c) 0) =
        b ^ 2 * (c ^ 2 + c - b) / c ^ 3 := by
    rw [hslope]
    simp [W, MazurTorsion.Kubert.tateNormalCurve, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negY]
    field_simp [hc]
    ring
  have h₄ : W.toAffine.Nonsingular
      (b * (b - c) / c ^ 2) (b ^ 2 * (c ^ 2 + c - b) / c ^ 3) := by
    have h :=
      WeierstrassCurve.Affine.nonsingular_add h₃ h00
        (fun hxy => hc hxy.left)
    rwa [hx, hy] at h
  refine ⟨h₄, ?_⟩
  rw [htriple]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hc]
  exact MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.some_eq_some W hx hy


end MazurTorsion.Kubert

namespace MazurTorsion.ExceptionalTwoTen



end MazurTorsion.ExceptionalTwoTen

end
end MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone

namespace MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



section
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- On Tate normal form, an origin killed by seven and not by lower
multiples satisfies `b² - bc - c³ = 0` with `c ≠ 0`. -/
theorem orderSeven_tate_relation
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (hP0 : (WeierstrassCurve.Affine.Point.some 0 0 h00 :
      (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Point) ≠ 0)
    (h7 : (7 : ℕ) • (WeierstrassCurve.Affine.Point.some 0 0 h00 :
      (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Point) = 0) :
    c ≠ 0 ∧ b ^ 2 - b * c - c ^ 3 = 0 := by
  set P : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00 with hPdef
  obtain ⟨h₃, htriple⟩ := MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.MazurTorsion.Kubert.three_nsmul_origin_coordinates b c hb h00
  have hc : c ≠ 0 := by
    intro hc0
    subst hc0
    have h3eq : (3 : ℕ) • P = -P := by
      rw [htriple, hPdef, WeierstrassCurve.Affine.Point.neg_some]
      exact MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.some_eq_some _ rfl
        (by norm_num [WeierstrassCurve.Affine.negY, MazurTorsion.Kubert.tateNormalCurve])
    have h4 : (4 : ℕ) • P = 0 := by
      have h4split : (4 : ℕ) • P = (3 : ℕ) • P + P := by abel
      rw [h4split, h3eq]
      abel
    apply hP0
    calc
      P = (2 : ℕ) • ((4 : ℕ) • P) - (7 : ℕ) • P := by abel
      _ = 0 := by rw [h4, h7]; simp
  refine ⟨hc, ?_⟩
  obtain ⟨h₄, hquad⟩ := MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.MazurTorsion.Kubert.four_mul_origin_coordinates b c hb hc h00
  have hfour : (4 : ℕ) • P = WeierstrassCurve.Affine.Point.some
      (b * (b - c) / c ^ 2) (b ^ 2 * (c ^ 2 + c - b) / c ^ 3) h₄ := by
    rw [hPdef, show (4 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
      WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 by abel]
    exact hquad
  have hthree : (3 : ℕ) • P = WeierstrassCurve.Affine.Point.some
      c (b - c) h₃ := by
    rw [hPdef]
    exact (MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.MazurTorsion.Kubert.three_nsmul_origin_coordinates b c hb h00).choose_spec
  have hsum : (4 : ℕ) • P = -((3 : ℕ) • P) := by
    rw [← add_eq_zero_iff_eq_neg]
    calc
      (4 : ℕ) • P + (3 : ℕ) • P = (7 : ℕ) • P := by abel
      _ = 0 := h7
  rw [hfour, hthree, WeierstrassCurve.Affine.Point.neg_some] at hsum
  have hx :=
    (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp hsum |>.1
  have hcleared : b * (b - c) = c ^ 3 := by
    field_simp at hx
    linarith [hx]
  linarith [hcleared]

/-- The order-seven relation is rationally parametrized by `d = b/c`. -/
theorem orderSeven_parametrization
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0)
    (hrel : b ^ 2 - b * c - c ^ 3 = 0) :
    ∃ d : ℚ, d ≠ 0 ∧ d ≠ 1 ∧
      b = d ^ 3 - d ^ 2 ∧ c = d ^ 2 - d := by
  refine ⟨b / c, div_ne_zero hb hc, ?_, ?_, ?_⟩
  · intro h1
    have hbc : b = c := by
      field_simp at h1
      linarith [h1]
    rw [hbc] at hrel
    have : c ^ 2 * c = 0 := by linarith [hrel]
    exact hc (by
      rcases mul_eq_zero.mp this with h | h
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
      · exact h)
  · field_simp
    linear_combination -hrel
  · field_simp
    linear_combination -hrel







end MazurTorsion.Kubert

end
end MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone

namespace MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/- Exact original arithmetic route for arbitrary elliptic curves over Q. Named consumer: the campaign’s full no-order49 contract. Complete original types and proof values retained. -/
namespace MazurTorsion.XZeroFortyNine
open _root_.MazurTorsion.Kubert (orderSevenG7F)

















/-- The explicit order-seven isogeny tower excludes rational points of exact
order `49`. -/
theorem rationalPoint_addOrderOf_ne_fortyNine
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : E.toAffine.Point) :
    addOrderOf P ≠ 49 := by
  intro h49
  have hnot : ∀ n : ℕ, ¬ (49 ∣ n) → (n : ℕ) • P ≠ 0 := by
    intro n hn hzero
    exact hn (h49 ▸ addOrderOf_dvd_of_nsmul_eq_zero hzero)
  let R : E.toAffine.Point := (7 : ℕ) • P
  have hRorder : addOrderOf R = 7 := by
    dsimp only [R]
    rw [addOrderOf_nsmul' P (by norm_num), h49]
    norm_num
  have hR0 : R ≠ 0 := by
    dsimp only [R]
    exact hnot 7 (by norm_num)
  have hR2 : R + R ≠ 0 := by
    intro hzero
    apply hnot 14 (by norm_num)
    simpa only [R, ← two_nsmul, ← mul_nsmul] using hzero
  have hR3 : R + R + R ≠ 0 := by
    intro hzero
    apply hnot 21 (by norm_num)
    calc
      (21 : ℕ) • P = (3 : ℕ) • ((7 : ℕ) • P) := by
        rw [← mul_nsmul]
      _ = R + R + R := by
        dsimp only [R]
        abel
      _ = 0 := hzero
  obtain ⟨b, c, u, hu, hb, h00, e, heR, hdisc, -, -⟩ :=
    MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.MazurTorsion.Kubert.exists_tateNormalCurve_scaled E R hR2 hR3
  have horigin0 :
      (WeierstrassCurve.Affine.Point.some 0 0 h00 :
        (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Point) ≠ 0 := by
    rw [← heR]
    exact fun hzero ↦ hR0 (e.injective (by simpa using hzero))
  have hsevenOrigin :
      (7 : ℕ) • (WeierstrassCurve.Affine.Point.some 0 0 h00 :
        (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Point) = 0 := by
    rw [← heR, ← map_nsmul]
    exact e.map_eq_zero_iff.mpr
      (hRorder ▸ addOrderOf_nsmul_eq_zero R)
  obtain ⟨hc, hrel⟩ :=
    MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.MazurTorsion.Kubert.orderSeven_tate_relation b c hb h00 horigin0 hsevenOrigin
  obtain ⟨d, hd0, hd1, hbeq, hceq⟩ :=
    MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.MazurTorsion.Kubert.orderSeven_parametrization b c hb hc hrel
  subst b
  subst c
  have hfamilyDelta :
      (MazurTorsion.Kubert.tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ ≠ 0 := by
    rw [← hdisc]
    exact mul_ne_zero (pow_ne_zero 12 hu) E.isUnit_Δ.ne_zero
  letI : (MazurTorsion.Kubert.orderSevenFamily d).IsElliptic := by
    rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
    simpa only [MazurTorsion.Kubert.orderSevenFamily, MazurTorsion.Kubert.orderSevenB,
      MazurTorsion.Kubert.orderSevenC] using hfamilyDelta
  change E.toAffine.Point ≃+
    (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point at e
  have heR' : e R = MazurTorsion.Kubert.orderSevenOrigin d := by
    exact heR.trans
      (MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.WeierstrassCurve.Affine.Point.some_eq_some _ rfl rfl)
  let Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point := e P
  have hQorder : addOrderOf Q = 49 := by
    dsimp only [Q]
    rw [AddEquiv.addOrderOf_eq]
    exact h49
  have hsevenQ : (7 : ℕ) • Q = MazurTorsion.Kubert.orderSevenOrigin d := by
    dsimp only [Q]
    rw [← map_nsmul]
    simpa only [R] using heR'
  have hkernel :
      MazurTorsion.Kubert.orderSevenPointMap d ((7 : ℕ) • Q) = 0 := by
    rw [hsevenQ]
    exact MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.MazurTorsion.Kubert.orderSevenPointMap_origin d
  obtain ⟨-, -, hK⟩ := MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.MazurTorsion.Kubert.orderSevenFamily_parameters_ne d
  obtain ⟨hres0, hres1, hres2⟩ :=
    MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.bounded_resultants_ne_zero
      d hd0 hd1 hK
  cases hQeq : Q with
  | zero =>
      rw [hQeq] at hQorder
      have hfalse : (1 : ℕ) = 49 := by
        rw [← hQorder]
        exact (addOrderOf_zero
          (G := (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point)).symm
      norm_num at hfalse
  | some x y hP =>
      rw [hQeq] at hQorder hkernel
      have hB :=
        (MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.MazurTorsion.Kubert.orderSevenResidualHauptmodul_spec_of_order_fortyNine_of_kernel
          hP hQorder hkernel).1
      have hG :=
        MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.MazurTorsion.Kubert.orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_bounded_resultants
          hP hQorder hkernel hres0 hres1 hres2
      exact MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.MazurTorsion.XZeroFortyNine.no_noncuspidal_correspondence_point
        (MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.MazurTorsion.Kubert.orderSevenFrickeParameter_ne_zero d) hB hG

end MazurTorsion.XZeroFortyNine



end MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone

theorem solution (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : E.toAffine.Point) :
    addOrderOf P ≠ 49 := by
  exact MazurTransfer.Order49DirectCurrentPointMapAndG7FCutsExactScopeRepairStandalone.MazurTorsion.XZeroFortyNine.rationalPoint_addOrderOf_ne_fortyNine E P
#print axioms solution
