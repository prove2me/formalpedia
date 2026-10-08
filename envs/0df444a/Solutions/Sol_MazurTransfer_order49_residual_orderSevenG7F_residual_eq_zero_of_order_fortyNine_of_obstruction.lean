-- Prove2me | solution 1 for MazurTransfer.order49_residual_orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T06:01:36.358817+00:00
-- url     : https://prove2.me/submissions/6a29d81a-7d3e-4d9e-8cb1-07b43763a054

import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49HauptmodulJNumerator
import Definitions.Def_MazurTransfer_Order49MarkedOriginPoint
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
import Definitions.Def_MazurTransfer_OrderFortyNinePlaneTransferData
import Mathlib
import Theorems.Thm_MazurTransfer_order49_geometry_orderSevenQuotient_discriminant
import Theorems.Thm_MazurTransfer_order49_geometry_orderSeven_discriminant
import Theorems.Thm_MazurTransfer_order49_marked_origin_orderSevenFamily_parameters_ne
import Theorems.Thm_MazurTransfer_order49_marked_origin_seven_nsmul_orderSevenOrigin
import Theorems.Thm_MazurTransfer_order49_point_map_addOrderOf_orderSevenPointMap_of_order_fortyNine
import Theorems.Thm_MazurTransfer_order49_point_map_addOrderOf_orderSevenPointMap_of_order_fortyNine_of_kernel
import Theorems.Thm_MazurTransfer_order49_point_map_orderSevenPointMap_kernel_killed_by_seven
import Theorems.Thm_MazurTransfer_order49_point_map_orderSevenPointMap_seven_nsmul_of_order_fortyNine
import Theorems.Thm_MazurTransfer_order49_point_map_orderSevenPointMap_some_eq_zero_iff
import Theorems.Thm_MazurTransfer_order49_point_map_orderSevenPointMap_some_of_not_kernelX
open Polynomial
open _root_.WeierstrassCurve
open _root_.WeierstrassCurve.Affine
open _root_.WeierstrassCurve.Affine.Point hiding neg_zero map_zero
theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.addOrderOf_orderSevenPointMap_of_order_fortyNine {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d ((7 : ℕ) • Q) = 0)
    (hmap : MazurTorsion.Kubert.orderSevenPointMap d ((7 : ℕ) • Q) =
      (7 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d Q) :
    addOrderOf (MazurTorsion.Kubert.orderSevenPointMap d Q) = 7 := by
  apply MazurTransfer.order49_point_map_addOrderOf_orderSevenPointMap_of_order_fortyNine <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.addOrderOf_orderSevenPointMap_of_order_fortyNine_of_kernel {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d ((7 : ℕ) • Q) = 0) :
    addOrderOf (MazurTorsion.Kubert.orderSevenPointMap d Q) = 7 := by
  apply MazurTransfer.order49_point_map_addOrderOf_orderSevenPointMap_of_order_fortyNine_of_kernel <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenFamily_parameters_ne (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    d ≠ 0 ∧ d ≠ 1 ∧
      d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0 := by
  apply MazurTransfer.order49_marked_origin_orderSevenFamily_parameters_ne <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenPointMap_kernel_killed_by_seven {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {P : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hP : MazurTorsion.Kubert.orderSevenPointMap d P = 0) :
    (7 : ℕ) • P = 0 := by
  apply MazurTransfer.order49_point_map_orderSevenPointMap_kernel_killed_by_seven <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenPointMap_seven_nsmul_of_order_fortyNine {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d ((7 : ℕ) • Q) = 0) :
    MazurTorsion.Kubert.orderSevenPointMap d ((7 : ℕ) • Q) =
      (7 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d Q := by
  apply MazurTransfer.order49_point_map_orderSevenPointMap_seven_nsmul_of_order_fortyNine <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenPointMap_some_eq_zero_iff {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y) :
    MazurTorsion.Kubert.orderSevenPointMap d (.some x y hP) = 0 ↔
      MazurTorsion.Kubert.OrderSevenKernelX d x := by
  apply MazurTransfer.order49_point_map_orderSevenPointMap_some_eq_zero_iff <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenPointMap_some_of_not_kernelX {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hx : ¬MazurTorsion.Kubert.OrderSevenKernelX d x) :
    MazurTorsion.Kubert.orderSevenPointMap d (.some x y hP) =
      MazurTorsion.Kubert.orderSevenVeluPoint hP
        (fun h ↦ hx (Or.inl h))
        (fun h ↦ hx (Or.inr (Or.inl h)))
        (fun h ↦ hx (Or.inr (Or.inr h))) := by
  apply MazurTransfer.order49_point_map_orderSevenPointMap_some_of_not_kernelX <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenQuotient_Δ (d : ℚ) :
    (MazurTorsion.Kubert.orderSevenQuotient d).Δ =
      d * (d - 1) * (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) ^ 7 := by
  apply MazurTransfer.order49_geometry_orderSevenQuotient_discriminant <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSeven_Δ (d : ℚ) :
    (MazurTorsion.Kubert.tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ =
      d ^ 7 * (d - 1) ^ 7 * (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) := by
  apply MazurTransfer.order49_geometry_orderSeven_discriminant <;> assumption

theorem MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.seven_nsmul_orderSevenOrigin (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    (7 : ℕ) • MazurTorsion.Kubert.orderSevenOrigin d = 0 := by
  apply MazurTransfer.order49_marked_origin_seven_nsmul_orderSevenOrigin <;> assumption
namespace MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



section
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Doubling

























/-- The completed-square cubic equals the square of the completed
ordinate on the affine curve. -/
theorem completedCubic_eq_completedY_sq
    (W : WeierstrassCurve ℚ) {x y : ℚ}
    (h : W.toAffine.Equation x y) :
    MazurTorsion.Doubling.completedCubic W x = (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
  rw [WeierstrassCurve.Affine.equation_iff] at h
  change y ^ 2 + W.a₁ * x * y + W.a₃ * y =
    x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ at h
  simp only [MazurTorsion.Doubling.completedCubic, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  linear_combination -4 * h





end MazurTorsion.Doubling

end
end MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers

namespace MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers
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
  rw [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.variableChange_negY] at hY
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
  simp only [addY, MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.variableChange_negAddY, MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.variableChange_addX, MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.variableChange_negY]

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
      rw [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.variableChange_negY]
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
  rw [Affine.Nonsingular, Affine.Nonsingular, MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.variableChange_equation W C,
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.variableChange_polynomialX W C, MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.variableChange_polynomialY W C]
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
      ((MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.variableChange_nonsingular W C x y).mpr h)

@[simp] lemma mapVariableChangeFun_zero : MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.mapVariableChangeFun W C 0 = 0 := rfl

lemma mapVariableChangeFun_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.mapVariableChangeFun W C (.some x y h)
      = .some ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
          ((MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.variableChange_nonsingular W C x y).mpr h) := rfl

lemma some_eq_some (W : WeierstrassCurve F) {x₁ x₂ y₁ y₂ : F} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : W.toAffine.Nonsingular x₁ y₁} {h₂ : W.toAffine.Nonsingular x₂ y₂} :
    (some x₁ y₁ h₁ : W.toAffine.Point) = some x₂ y₂ h₂ := by
  subst hx hy
  rfl

lemma mapVariableChangeFun_injective :
    Function.Injective (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.mapVariableChangeFun W C) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · simp [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.mapVariableChangeFun] at h
  · simp [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.mapVariableChangeFun] at h
  · rw [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.mapVariableChangeFun_some, MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.mapVariableChangeFun_some] at h
    injection h with hX hY
    have hx : x₁ = x₂ := mul_left_cancel₀ (pow_ne_zero 2 hu) (by linear_combination hX)
    exact MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.some_eq_some (C • W) hx
      (mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination hY - (C.u : F) ^ 2 * C.s * hx))

variable [DecidableEq F]

/-- Transport of the affine point group along an equality of Weierstrass curves. -/
def equivOfEq {V V' : WeierstrassCurve F} (h : V = V') :
    V.toAffine.Point ≃+ V'.toAffine.Point := by
  subst h
  exact AddEquiv.refl _

@[simp] lemma equivOfEq_some {V V' : WeierstrassCurve F} (h : V = V') {x y : F}
    (hns : V.toAffine.Nonsingular x y) :
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.equivOfEq h (some x y hns) = some x y (h ▸ hns) := by
  subst h
  rfl

/-- The group homomorphism induced by the admissible change of variables. -/
def mapVariableChange : (C • W).toAffine.Point →+ W.toAffine.Point where
  toFun := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.mapVariableChangeFun W C
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    simp only [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.mapVariableChangeFun_some]
    have e₁ : (C • W).toAffine.Equation x₁ y₁ := h₁.left
    have e₂ : (C • W).toAffine.Equation x₂ y₂ := h₂.left
    by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
    · rw [add_of_Y_eq hxy.1 hxy.2, MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.mapVariableChangeFun_zero]
      refine (add_of_Y_eq ?_ ?_).symm
      · rw [hxy.1]
      · rw [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.variableChange_negY, hxy.2, hxy.1]
    · rw [add_some hxy, MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.mapVariableChangeFun_some, add_some (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.variableChange_negY_ne W C hxy)]
      simp only [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.variableChange_slope W C e₁ e₂ hxy, MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.variableChange_addX, MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.variableChange_addY]

/-- The point-group isomorphism induced by the admissible change of variables. -/
def equivVariableChange : (C • W).toAffine.Point ≃+ W.toAffine.Point :=
  have hright : ∀ P, MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.mapVariableChangeFun W C
      (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.mapVariableChangeFun (C • W) C⁻¹ (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.equivOfEq (inv_smul_smul C W).symm P)) = P := by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    rintro (_ | ⟨X, Y, h⟩)
    · simp [← zero_def]
    · rw [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.equivOfEq_some, MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.mapVariableChangeFun_some, MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.mapVariableChangeFun_some]
      refine MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.some_eq_some W ?_ ?_ <;>
        (simp only [VariableChange.inv_def, Units.val_inv_eq_inv_val]; field)
  { toFun := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.mapVariableChangeFun W C
    invFun := fun P ↦ MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.mapVariableChangeFun (C • W) C⁻¹ (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.equivOfEq (inv_smul_smul C W).symm P)
    left_inv := Function.RightInverse.leftInverse_of_injective hright
      (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.mapVariableChangeFun_injective W C)
    right_inv := hright
    map_add' := (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.mapVariableChange W C).map_add' }

lemma equivVariableChange_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.equivVariableChange W C (.some x y h)
      = .some ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
          ((MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.variableChange_nonsingular W C x y).mpr h) := rfl

end Point

end WeierstrassCurve.Affine

end

end MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers

namespace MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





namespace MazurTorsion.OddPrimeFullTorsion

open Polynomial
open scoped WeierstrassCurve.Affine















/-- The forward division-polynomial root criterion needed by the discriminant argument.

Mathlib currently defines the division polynomials but does not yet connect their evaluation to
scalar multiplication of affine points. -/
def HasDivisionPolynomialRootCriterion
    (W : WeierstrassCurve ℚ) (n : ℕ) : Prop :=
  ∀ {x y : ℚ} (hP : W.toAffine.Nonsingular x y),
    n • WeierstrassCurve.Affine.Point.some x y hP = 0 →
      Polynomial.eval x (W.preΨ' n) = 0



























end MazurTorsion.OddPrimeFullTorsion

end MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers

namespace MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers
/-
Copyright (c) 2026 Victor Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor Aguiar
-/





namespace MazurTorsion.ThreeTorsion

open WeierstrassCurve



/-- The exact algebraic identity behind the three-division polynomial:
on the curve, the value of `Ψ₃` is the negative square of the tangent
denominator times the difference between the doubled and original
x-coordinates. -/
lemma three_division_tangent_identity
    {a₁ a₂ a₃ a₄ a₆ x y slope : ℚ}
    (hcurve :
      y ^ 2 + a₁ * x * y + a₃ * y =
        x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hslope :
      slope * (2 * y + a₁ * x + a₃) =
        3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y) :
    3 * x ^ 4 + (a₁ ^ 2 + 4 * a₂) * x ^ 3 +
        3 * (a₁ * a₃ + 2 * a₄) * x ^ 2 +
        3 * (a₃ ^ 2 + 4 * a₆) * x +
        (a₁ ^ 2 * a₆ + 4 * a₂ * a₆ - a₁ * a₃ * a₄ +
          a₂ * a₃ ^ 2 - a₄ ^ 2) =
      -(2 * y + a₁ * x + a₃) ^ 2 *
        (slope ^ 2 + a₁ * slope - a₂ - 3 * x) := by
  linear_combination
    ((3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y) +
      slope * (2 * y + a₁ * x + a₃) +
      a₁ * (2 * y + a₁ * x + a₃)) * hslope -
    (a₁ ^ 2 + 4 * a₂ + 12 * x) * hcurve

open scoped WeierstrassCurve.Affine



















end MazurTorsion.ThreeTorsion

end MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers

namespace MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



section
namespace MazurTorsion.Kubert







/-- The cross-multiplied equality of the two level-seven `j`-values factors
as the diagonal times the correspondence polynomial. -/
theorem orderSevenJNumerator_crossDifference (s B : ℚ) :
    MazurTorsion.Kubert.orderSevenJNumerator s * B ^ 7 - MazurTorsion.Kubert.orderSevenJNumerator B * s ^ 7 =
      (s - B) * MazurTorsion.Kubert.orderSevenG7F s B := by
  simp only [MazurTorsion.Kubert.orderSevenJNumerator, MazurTorsion.Kubert.orderSevenG7F]
  ring

/-- Off the diagonal, equality of the cross-multiplied level-seven
`j`-values is exactly the correspondence equation. -/
theorem orderSevenG7F_eq_zero_iff_crossMultiply
    {s B : ℚ} (hsB : s ≠ B) :
    MazurTorsion.Kubert.orderSevenG7F s B = 0 ↔
      MazurTorsion.Kubert.orderSevenJNumerator s * B ^ 7 =
        MazurTorsion.Kubert.orderSevenJNumerator B * s ^ 7 := by
  constructor
  · intro hG
    apply sub_eq_zero.mp
    rw [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenJNumerator_crossDifference, hG, mul_zero]
  · intro hJ
    have hprod : (s - B) * MazurTorsion.Kubert.orderSevenG7F s B = 0 := by
      rw [← MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenJNumerator_crossDifference]
      exact sub_eq_zero.mpr hJ
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hsB)









end MazurTorsion.Kubert

end
end MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers

namespace MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



section
namespace MazurTorsion.Kubert

/-- The numerator of the tangent slope used in pointwise Tate
normalization. -/
def pointTateLambdaNumerator
    (W : WeierstrassCurve ℚ) (x y : ℚ) : ℚ :=
  W.a₄ + 2 * x * W.a₂ - y * W.a₁ + 3 * x ^ 2

/-- The numerator of `pointTateAlpha` after clearing
`pointTateBeta ^ 2`. -/
def pointTateAlphaCleared
    (W : WeierstrassCurve ℚ) (x y : ℚ) : ℚ :=
  (W.a₂ + 3 * x) * MazurTorsion.Kubert.pointTateBeta W x y ^ 2 -
    W.a₁ * MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateLambdaNumerator W x y * MazurTorsion.Kubert.pointTateBeta W x y -
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateLambdaNumerator W x y ^ 2

/-- The last linear factor in `pointTateParameter`, after clearing
`pointTateBeta ^ 3`. -/
def pointTateGammaCleared
    (W : WeierstrassCurve ℚ) (x y : ℚ) : ℚ :=
  MazurTorsion.Kubert.pointTateBeta W x y ^ 4 -
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateAlphaCleared W x y *
      (W.a₁ * MazurTorsion.Kubert.pointTateBeta W x y +
        2 * MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateLambdaNumerator W x y)

/-- The numerator of the pointwise Tate parameter in fully cleared form. -/
def pointTateParameterClearedNumerator
    (W : WeierstrassCurve ℚ) (x y : ℚ) : ℚ :=
  -MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateAlphaCleared W x y ^ 3

/-- The denominator of the pointwise Tate parameter in fully cleared
form. -/
def pointTateParameterClearedDenominator
    (W : WeierstrassCurve ℚ) (x y : ℚ) : ℚ :=
  MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateGammaCleared W x y * MazurTorsion.Kubert.pointTateBeta W x y ^ 4

/-- The pointwise Tate parameter as a quotient of polynomial expressions.

No nonvanishing hypothesis on the cleared denominator is needed: Lean's
division is total, and both sides are zero when the last normalization
factor vanishes. -/
theorem pointTateParameter_eq_cleared
    (W : WeierstrassCurve ℚ) {x y : ℚ}
    (hbeta : MazurTorsion.Kubert.pointTateBeta W x y ≠ 0) :
    MazurTorsion.Kubert.pointTateParameter W x y =
      MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateParameterClearedNumerator W x y /
        MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateParameterClearedDenominator W x y := by
  simp only [MazurTorsion.Kubert.pointTateParameter, MazurTorsion.Kubert.pointTateAlpha, MazurTorsion.Kubert.pointTateLambda,
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateLambdaNumerator, MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateAlphaCleared,
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateGammaCleared, MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateParameterClearedNumerator,
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateParameterClearedDenominator]
  field_simp [hbeta]
  ring

/-- A nonzero pointwise level-seven Hauptmodul forces the vertical tangent
denominator used by Tate normalization to be nonzero. -/
theorem pointTateBeta_ne_zero_of_hauptmodul_ne_zero
    (W : WeierstrassCurve ℚ) {x y : ℚ}
    (hB : MazurTorsion.Kubert.orderSevenHauptmodulAt W x y ≠ 0) :
    MazurTorsion.Kubert.pointTateBeta W x y ≠ 0 := by
  have ht : MazurTorsion.Kubert.pointTateParameter W x y ≠ 0 := by
    intro ht
    apply hB
    simp [MazurTorsion.Kubert.orderSevenHauptmodulAt, ht]
  have hden :
      MazurTorsion.Kubert.pointTateBeta W x y *
        (MazurTorsion.Kubert.pointTateBeta W x y - MazurTorsion.Kubert.pointTateAlpha W x y *
          (W.a₁ + 2 * MazurTorsion.Kubert.pointTateLambda W x y)) ≠ 0 := by
    exact (div_ne_zero_iff.mp (by
      simpa only [MazurTorsion.Kubert.pointTateParameter] using ht)).2
  exact (mul_ne_zero_iff.mp hden).1





/-- The pointwise level-seven Hauptmodul as a quotient of its fully
polynomial numerator and denominator. -/
theorem orderSevenHauptmodulAt_eq_cleared
    (W : WeierstrassCurve ℚ) {x y : ℚ}
    (hbeta : MazurTorsion.Kubert.pointTateBeta W x y ≠ 0) :
    MazurTorsion.Kubert.orderSevenHauptmodulAt W x y =
      MazurTorsion.Kubert.orderSevenParameterHauptmodulNumerator
          (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateParameterClearedNumerator W x y)
          (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateParameterClearedDenominator W x y) /
        MazurTorsion.Kubert.orderSevenParameterCubic
          (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateParameterClearedNumerator W x y)
          (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateParameterClearedDenominator W x y) := by
  rw [show MazurTorsion.Kubert.orderSevenHauptmodulAt W x y =
      49 * MazurTorsion.Kubert.pointTateParameter W x y *
          (MazurTorsion.Kubert.pointTateParameter W x y - 1) /
        (MazurTorsion.Kubert.pointTateParameter W x y ^ 3 -
          8 * MazurTorsion.Kubert.pointTateParameter W x y ^ 2 +
          5 * MazurTorsion.Kubert.pointTateParameter W x y + 1) by
    rfl]
  rw [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateParameter_eq_cleared W hbeta]
  let A := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateParameterClearedNumerator W x y
  let B := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateParameterClearedDenominator W x y
  change 49 * (A / B) * (A / B - 1) /
      ((A / B) ^ 3 - 8 * (A / B) ^ 2 + 5 * (A / B) + 1) =
    MazurTorsion.Kubert.orderSevenParameterHauptmodulNumerator A B /
      MazurTorsion.Kubert.orderSevenParameterCubic A B
  by_cases hB : B = 0
  · simp [hB, MazurTorsion.Kubert.orderSevenParameterHauptmodulNumerator,
      MazurTorsion.Kubert.orderSevenParameterCubic]
  · have hden :
        (A / B) ^ 3 - 8 * (A / B) ^ 2 + 5 * (A / B) + 1 =
          MazurTorsion.Kubert.orderSevenParameterCubic A B / B ^ 3 := by
      simp only [MazurTorsion.Kubert.orderSevenParameterCubic]
      field_simp [hB]
    rw [hden]
    by_cases hC : MazurTorsion.Kubert.orderSevenParameterCubic A B = 0
    · simp [hC]
    · field_simp [hB, hC]
      simp only [MazurTorsion.Kubert.orderSevenParameterHauptmodulNumerator]
      ring

end MazurTorsion.Kubert

end
end MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers

namespace MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





namespace MazurTorsion.DivisionPolynomialRootCriterion

open Polynomial
open scoped WeierstrassCurve.Affine

private lemma exists_coordinates_of_ne_zero
    (W : WeierstrassCurve ℚ) (P : W.toAffine.Point)
    (hP : P ≠ 0) :
    ∃ x y, ∃ h : W.toAffine.Nonsingular x y,
      P = WeierstrassCurve.Affine.Point.some x y h := by
  cases P with
  | zero => exact (hP rfl).elim
  | some x y h => exact ⟨x, y, h, rfl⟩

private lemma double_abscissa_formula
    (W : WeierstrassCurve ℚ) {x y x₂ y₂ : ℚ}
    (hP : W.toAffine.Nonsingular x y)
    (hP₂ : W.toAffine.Nonsingular x₂ y₂)
    (hdouble :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP =
        WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂) :
    Polynomial.eval x (W.Φ 2) =
      x₂ * Polynomial.eval x (W.ΨSq 2) := by
  have hy : y ≠ W.toAffine.negY x y := by
    intro hy
    have hzero :
        (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP = 0 := by
      rw [two_nsmul,
        WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy]
    rw [hzero] at hdouble
    exact WeierstrassCurve.Affine.Point.some_ne_zero hP₂ hdouble.symm
  let slope := W.toAffine.slope x x y y
  have hadd :=
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁ := hP) hy
  have hx₂ : W.toAffine.addX x x slope = x₂ := by
    have hsum :
        WeierstrassCurve.Affine.Point.some x y hP +
            WeierstrassCurve.Affine.Point.some x y hP =
          WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ := by
      simpa [two_nsmul] using hdouble
    exact (WeierstrassCurve.Affine.Point.some.inj
      (hadd.symm.trans hsum)).1
  have hden : y - W.toAffine.negY x y =
      2 * y + W.a₁ * x + W.a₃ := by
    simp only [WeierstrassCurve.Affine.negY]
    ring
  have hden_ne : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    rw [← hden]
    exact sub_ne_zero.mpr hy
  have hslope :
      slope =
        (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) /
          (2 * y + W.a₁ * x + W.a₃) := by
    dsimp [slope]
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy, hden]
  have hslope_mul :
      slope * (2 * y + W.a₁ * x + W.a₃) =
        3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    rw [hslope, div_mul_cancel₀ _ hden_ne]
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  have hD :
      (2 * y + W.a₁ * x + W.a₃) ^ 2 =
        Polynomial.eval x (W.ΨSq 2) := by
    simp only [WeierstrassCurve.ΨSq_two, WeierstrassCurve.Ψ₂Sq,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    linear_combination 4 * hcurve
  have hψ₃ :=
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.ThreeTorsion.three_division_tangent_identity hcurve hslope_mul
  have hx₂' : slope ^ 2 + W.a₁ * slope - W.a₂ - 2 * x = x₂ := by
    simp only [WeierstrassCurve.Affine.addX] at hx₂
    linear_combination hx₂
  have hψ₃eval :
      Polynomial.eval x W.Ψ₃ =
        -(2 * y + W.a₁ * x + W.a₃) ^ 2 *
          (slope ^ 2 + W.a₁ * slope - W.a₂ - 3 * x) := by
    simp only [WeierstrassCurve.Ψ₃, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_ofNat, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    linear_combination hψ₃
  have hΦ :
      Polynomial.eval x (W.Φ 2) =
        x * Polynomial.eval x (W.ΨSq 2) -
          Polynomial.eval x W.Ψ₃ := by
    simp only [WeierstrassCurve.Φ_two, WeierstrassCurve.ΨSq_two,
      WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
      Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_ofNat,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  calc
    Polynomial.eval x (W.Φ 2) =
        x * Polynomial.eval x (W.ΨSq 2) -
          Polynomial.eval x W.Ψ₃ := hΦ
    _ = x * Polynomial.eval x (W.ΨSq 2) +
        (2 * y + W.a₁ * x + W.a₃) ^ 2 *
          (slope ^ 2 + W.a₁ * slope - W.a₂ - 3 * x) := by
            rw [hψ₃eval]
            ring
    _ = x * Polynomial.eval x (W.ΨSq 2) +
        Polynomial.eval x (W.ΨSq 2) * (x₂ - x) := by
            rw [hD]
            linear_combination
              Polynomial.eval x (W.ΨSq 2) * hx₂'
    _ = x₂ * Polynomial.eval x (W.ΨSq 2) := by ring

private lemma preΨ_four_double_formula
    (W : WeierstrassCurve ℚ) {x y x₂ y₂ : ℚ}
    (hP : W.toAffine.Nonsingular x y)
    (hP₂ : W.toAffine.Nonsingular x₂ y₂)
    (hdouble :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP =
        WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂) :
    Polynomial.eval x W.preΨ₄ =
      (2 * y + W.a₁ * x + W.a₃) ^ 3 *
        (2 * y₂ + W.a₁ * x₂ + W.a₃) := by
  have hy : y ≠ W.toAffine.negY x y := by
    intro hy
    have hzero :
        (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP = 0 := by
      rw [two_nsmul,
        WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy]
    rw [hzero] at hdouble
    exact WeierstrassCurve.Affine.Point.some_ne_zero hP₂ hdouble.symm
  let slope := W.toAffine.slope x x y y
  have hadd :=
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁ := hP) hy
  have hsum :
      WeierstrassCurve.Affine.Point.some x y hP +
          WeierstrassCurve.Affine.Point.some x y hP =
        WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ := by
    simpa [two_nsmul] using hdouble
  have hcoords :=
    WeierstrassCurve.Affine.Point.some.inj (hadd.symm.trans hsum)
  have hx₂ : slope ^ 2 + W.a₁ * slope - W.a₂ - 2 * x = x₂ := by
    have hx := hcoords.1
    simp only [WeierstrassCurve.Affine.addX] at hx
    linear_combination hx
  have hy₂ :
      y₂ = -(slope * (x₂ - x) + y) - W.a₁ * x₂ - W.a₃ := by
    have hycoord := hcoords.2
    simp only [WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY] at hycoord
    rw [hcoords.1] at hycoord
    change
      -(slope * (x₂ - x) + y) - W.a₁ * x₂ - W.a₃ = y₂
      at hycoord
    exact hycoord.symm
  have hden : y - W.toAffine.negY x y =
      2 * y + W.a₁ * x + W.a₃ := by
    simp only [WeierstrassCurve.Affine.negY]
    ring
  have hslope_mul :
      slope * (2 * y + W.a₁ * x + W.a₃) =
        3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    dsimp [slope]
    rw [← hden, WeierstrassCurve.Affine.slope_of_Y_ne rfl hy,
      div_mul_cancel₀ _ (sub_ne_zero.mpr hy)]
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  have hψ :=
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.ThreeTorsion.three_division_tangent_identity hcurve hslope_mul
  have hψeval :
      Polynomial.eval x W.Ψ₃ =
        -(2 * y + W.a₁ * x + W.a₃) ^ 2 * (x₂ - x) := by
    simp only [WeierstrassCurve.Ψ₃, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_ofNat, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    linear_combination hψ -
      (2 * y + W.a₁ * x + W.a₃) ^ 2 * hx₂
  have hvertical :
      2 * y₂ + W.a₁ * x₂ + W.a₃ =
        -(2 * slope + W.a₁) * (x₂ - x) -
          (2 * y + W.a₁ * x + W.a₃) := by
    linear_combination 2 * hy₂
  have hpre :
      Polynomial.eval x W.preΨ₄ =
        (2 * y + W.a₁ * x + W.a₃) *
            (2 * slope + W.a₁) * Polynomial.eval x W.Ψ₃ -
          (2 * y + W.a₁ * x + W.a₃) ^ 4 := by
    simp only [WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₃,
      Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_ofNat, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    linear_combination
      -2 * (3 * x ^ 4 + (W.a₁ ^ 2 + 4 * W.a₂) * x ^ 3 +
        3 * (W.a₁ * W.a₃ + 2 * W.a₄) * x ^ 2 +
        3 * (W.a₃ ^ 2 + 4 * W.a₆) * x +
        (W.a₁ ^ 2 * W.a₆ + 4 * W.a₂ * W.a₆ -
          W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 -
          W.a₄ ^ 2)) * hslope_mul +
      8 * ((2 * y + W.a₁ * x + W.a₃) ^ 2 -
        2 * (y ^ 2 + W.a₁ * x * y + W.a₃ * y -
          (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))) * hcurve
  calc
    Polynomial.eval x W.preΨ₄ =
        (2 * y + W.a₁ * x + W.a₃) *
            (2 * slope + W.a₁) * Polynomial.eval x W.Ψ₃ -
          (2 * y + W.a₁ * x + W.a₃) ^ 4 := hpre
    _ = (2 * y + W.a₁ * x + W.a₃) ^ 3 *
        (2 * y₂ + W.a₁ * x₂ + W.a₃) := by
          rw [hψeval, hvertical]
          ring

private lemma two_cross_identity
    (W : WeierstrassCurve ℚ) (x : ℚ) :
    Polynomial.eval x (W.Φ 2) =
      x * Polynomial.eval x (W.ΨSq 2) -
        Polynomial.eval x W.Ψ₃ := by
  simp only [WeierstrassCurve.Φ_two, WeierstrassCurve.ΨSq_two,
    WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

private lemma triple_abscissa_formula
    (W : WeierstrassCurve ℚ) {x y x₂ y₂ x₃ y₃ : ℚ}
    (hP : W.toAffine.Nonsingular x y)
    (hP₂ : W.toAffine.Nonsingular x₂ y₂)
    (hP₃ : W.toAffine.Nonsingular x₃ y₃)
    (hdouble :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP =
        WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂)
    (htriple :
      (3 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP =
        WeierstrassCurve.Affine.Point.some x₃ y₃ hP₃) :
    Polynomial.eval x (W.Φ 3) =
      x₃ * Polynomial.eval x (W.ΨSq 3) := by
  let P := WeierstrassCurve.Affine.Point.some x y hP
  let P₂ := WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂
  have hP_ne : P ≠ 0 :=
    WeierstrassCurve.Affine.Point.some_ne_zero hP
  have hx : x ≠ x₂ := by
    intro hx
    rcases (WeierstrassCurve.Affine.Point.X_eq_iff).mp hx with heq | heq
    · apply hP_ne
      have htwice : (2 : ℕ) • P = P :=
        hdouble.trans heq.symm
      rw [two_nsmul] at htwice
      have hcancel : P + P = P + 0 := by
        exact htwice.trans (add_zero P).symm
      exact add_left_cancel hcancel
    · have hneg : P = -((2 : ℕ) • P) := by
        rw [hdouble]
        exact heq
      have hzero : (3 : ℕ) • P = 0 := by
        have hsum : P + (2 : ℕ) • P = 0 :=
          (add_eq_zero_iff_eq_neg).2 hneg
        rw [show (3 : ℕ) = 1 + 2 by norm_num,
          add_nsmul, one_nsmul]
        exact hsum
      change (3 : ℕ) • P =
        WeierstrassCurve.Affine.Point.some x₃ y₃ hP₃ at htriple
      rw [hzero] at htriple
      exact WeierstrassCurve.Affine.Point.some_ne_zero hP₃
        htriple.symm
  have hadd :
      P + P₂ = WeierstrassCurve.Affine.Point.some x₃ y₃ hP₃ := by
    change
      WeierstrassCurve.Affine.Point.some x y hP +
          WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ =
        WeierstrassCurve.Affine.Point.some x₃ y₃ hP₃
    rw [← hdouble]
    rw [← htriple]
    rw [show (3 : ℕ) = 1 + 2 by norm_num,
      add_nsmul, one_nsmul]
  have hadd_formula :=
    WeierstrassCurve.Affine.Point.add_of_X_ne
      (W := W.toAffine) (h₁ := hP) (h₂ := hP₂) hx
  have hx_add :
      W.toAffine.addX x x₂ (W.toAffine.slope x x₂ y y₂) = x₃ :=
    (WeierstrassCurve.Affine.Point.some.inj
      (hadd_formula.symm.trans hadd)).1
  have hsub :
      P + (-P₂) = -P := by
    change
      WeierstrassCurve.Affine.Point.some x y hP +
          (-WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂) =
        -WeierstrassCurve.Affine.Point.some x y hP
    rw [← hdouble]
    rw [two_nsmul]
    abel
  have hP₂neg :
      W.toAffine.Nonsingular x₂ (W.toAffine.negY x₂ y₂) :=
    (W.toAffine.nonsingular_neg x₂ y₂).mpr hP₂
  have hsub_formula :=
    WeierstrassCurve.Affine.Point.add_of_X_ne
      (W := W.toAffine) (h₁ := hP) (h₂ := hP₂neg) hx
  have hx_sub :
      W.toAffine.addX x x₂
          (W.toAffine.slope x x₂ y (W.toAffine.negY x₂ y₂)) = x := by
    have heq := hsub_formula.symm.trans hsub
    exact (WeierstrassCurve.Affine.Point.some.inj heq).1
  have haddX :=
    W.toAffine.addX_eq_addX_negY_sub y y₂ hx
  rw [hx_add, hx_sub] at haddX
  have hvertical :
      y - W.toAffine.negY x y =
        2 * y + W.a₁ * x + W.a₃ := by
    simp only [WeierstrassCurve.Affine.negY]
    ring
  have hvertical₂ :
      y₂ - W.toAffine.negY x₂ y₂ =
        2 * y₂ + W.a₁ * x₂ + W.a₃ := by
    simp only [WeierstrassCurve.Affine.negY]
    ring
  rw [hvertical, hvertical₂] at haddX
  have hden_ne : x₂ - x ≠ 0 :=
    sub_ne_zero.mpr hx.symm
  have hsecant :
      (x₂ - x) ^ 2 * (x - x₃) =
        (2 * y + W.a₁ * x + W.a₃) *
          (2 * y₂ + W.a₁ * x₂ + W.a₃) := by
    field_simp [hden_ne] at haddX
    linear_combination -haddX
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  have hD :
      Polynomial.eval x (W.ΨSq 2) =
        (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
    simp only [WeierstrassCurve.ΨSq_two,
      WeierstrassCurve.Ψ₂Sq, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    linear_combination -4 * hcurve
  have hA :=
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.DivisionPolynomialRootCriterion.double_abscissa_formula W hP hP₂ hdouble
  have htwo := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.DivisionPolynomialRootCriterion.two_cross_identity W x
  have hψ :
      Polynomial.eval x W.Ψ₃ =
        -(2 * y + W.a₁ * x + W.a₃) ^ 2 * (x₂ - x) := by
    linear_combination htwo - hA -
      (x₂ - x) * hD
  have hpre :=
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.DivisionPolynomialRootCriterion.preΨ_four_double_formula W hP hP₂ hdouble
  have hD₂ :
      Polynomial.eval x W.Ψ₂Sq =
        (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
    simpa only [WeierstrassCurve.ΨSq_two] using hD
  simp only [WeierstrassCurve.Φ_three,
    WeierstrassCurve.ΨSq_three, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  rw [hpre, hD₂, hψ]
  linear_combination
    (2 * y + W.a₁ * x + W.a₃) ^ 4 * hsecant

private lemma four_Φ_composition
    (W : WeierstrassCurve ℚ) (x : ℚ) :
    let A := Polynomial.eval x (W.Φ 2)
    let D := Polynomial.eval x (W.ΨSq 2)
    Polynomial.eval x (W.Φ 4) =
      A ^ 4 - W.b₄ * A ^ 2 * D ^ 2 -
        2 * W.b₆ * A * D ^ 3 - W.b₈ * D ^ 4 := by
  dsimp
  simp only [WeierstrassCurve.Φ_four, WeierstrassCurve.Φ_two,
    WeierstrassCurve.ΨSq_two,
    WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.preΨ₄, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

private lemma four_ΨSq_composition
    (W : WeierstrassCurve ℚ) (x : ℚ) :
    let A := Polynomial.eval x (W.Φ 2)
    let D := Polynomial.eval x (W.ΨSq 2)
    Polynomial.eval x (W.ΨSq 4) =
      4 * A ^ 3 * D + W.b₂ * A ^ 2 * D ^ 2 +
        2 * W.b₄ * A * D ^ 3 + W.b₆ * D ^ 4 := by
  dsimp
  simp only [WeierstrassCurve.ΨSq_four,
    WeierstrassCurve.Φ_two, WeierstrassCurve.ΨSq_two,
    WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.preΨ₄,
    Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

private lemma quadruple_abscissa_formula
    (W : WeierstrassCurve ℚ) {x y x₂ y₂ x₄ y₄ : ℚ}
    (hP : W.toAffine.Nonsingular x y)
    (hP₂ : W.toAffine.Nonsingular x₂ y₂)
    (hP₄ : W.toAffine.Nonsingular x₄ y₄)
    (hdouble :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP =
        WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂)
    (hdouble₂ :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ =
        WeierstrassCurve.Affine.Point.some x₄ y₄ hP₄) :
    Polynomial.eval x (W.Φ 4) =
      x₄ * Polynomial.eval x (W.ΨSq 4) := by
  have hA :=
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.DivisionPolynomialRootCriterion.double_abscissa_formula W hP hP₂ hdouble
  have hA₂ :=
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.DivisionPolynomialRootCriterion.double_abscissa_formula W hP₂ hP₄ hdouble₂
  have hΦ :
      Polynomial.eval x (W.Φ 4) =
        Polynomial.eval x (W.ΨSq 2) ^ 4 *
          Polynomial.eval x₂ (W.Φ 2) := by
    rw [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.DivisionPolynomialRootCriterion.four_Φ_composition]
    rw [hA]
    simp only [WeierstrassCurve.Φ_two, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X]
    ring
  have hΨ :
      Polynomial.eval x (W.ΨSq 4) =
        Polynomial.eval x (W.ΨSq 2) ^ 4 *
          Polynomial.eval x₂ (W.ΨSq 2) := by
    rw [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.DivisionPolynomialRootCriterion.four_ΨSq_composition]
    rw [hA]
    simp only [WeierstrassCurve.ΨSq_two,
      WeierstrassCurve.Ψ₂Sq, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X]
    ring
  rw [hΦ, hA₂, hΨ]
  ring



private lemma seven_cross_identity
    (W : WeierstrassCurve ℚ) (x : ℚ) :
    Polynomial.eval x (W.Φ 4) *
          Polynomial.eval x (W.ΨSq 3) -
        Polynomial.eval x (W.Φ 3) *
          Polynomial.eval x (W.ΨSq 4) =
      -Polynomial.eval x (W.preΨ' 7) := by
  have hfive :
      W.preΨ' 5 = W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3 := by
    rw [show (5 : ℕ) = 2 * (0 + 2) + 1 by norm_num,
      W.preΨ'_odd 0]
    norm_num
  have hseven :
      W.preΨ' 7 =
        (W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3) * W.Ψ₃ ^ 3 -
          W.preΨ₄ ^ 3 * W.Ψ₂Sq ^ 2 := by
    rw [show (7 : ℕ) = 2 * (1 + 2) + 1 by norm_num,
      W.preΨ'_odd 1]
    norm_num [hfive]
  rw [hseven]
  simp only [WeierstrassCurve.Φ_four,
    WeierstrassCurve.Φ_three, WeierstrassCurve.ΨSq_four,
    WeierstrassCurve.ΨSq_three, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  ring



/-- The forward seventh-division-polynomial root criterion over `ℚ`. -/
theorem hasDivisionPolynomialRootCriterion_seven
    (W : WeierstrassCurve ℚ) :
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.OddPrimeFullTorsion.HasDivisionPolynomialRootCriterion W 7 := by
  intro x y hP hseven
  let P := WeierstrassCurve.Affine.Point.some x y hP
  have hP_ne : P ≠ 0 :=
    WeierstrassCurve.Affine.Point.some_ne_zero hP
  have htwo_ne : (2 : ℕ) • P ≠ 0 := by
    intro htwo
    apply hP_ne
    have hsplit :
        (7 : ℕ) • P =
          (2 : ℕ) • P + (2 : ℕ) • P + (2 : ℕ) • P + P := by
      rw [show (7 : ℕ) = 2 + 2 + 2 + 1 by norm_num,
        add_nsmul, add_nsmul, add_nsmul, one_nsmul]
    change (7 : ℕ) • P = 0 at hseven
    rw [hsplit, htwo, zero_add, zero_add, zero_add] at hseven
    exact hseven
  have hthree_ne : (3 : ℕ) • P ≠ 0 := by
    intro hthree
    apply hP_ne
    have hsplit :
        (7 : ℕ) • P = (3 : ℕ) • P + (3 : ℕ) • P + P := by
      rw [show (7 : ℕ) = 3 + 3 + 1 by norm_num,
        add_nsmul, add_nsmul, one_nsmul]
    change (7 : ℕ) • P = 0 at hseven
    rw [hsplit, hthree, zero_add, zero_add] at hseven
    exact hseven
  have hfour_ne : (4 : ℕ) • P ≠ 0 := by
    intro hfour
    apply hP_ne
    have hsplitSeven :
        (7 : ℕ) • P = (4 : ℕ) • P + (3 : ℕ) • P := by
      rw [show (7 : ℕ) = 4 + 3 by norm_num, add_nsmul]
    have hthree : (3 : ℕ) • P = 0 := by
      change (7 : ℕ) • P = 0 at hseven
      rw [hsplitSeven, hfour, zero_add] at hseven
      exact hseven
    have hsplitFour :
        (4 : ℕ) • P = (3 : ℕ) • P + P := by
      rw [show (4 : ℕ) = 3 + 1 by norm_num,
        add_nsmul, one_nsmul]
    rw [hsplitFour, hthree, zero_add] at hfour
    exact hfour
  obtain ⟨x₂, y₂, hP₂, hdouble⟩ :=
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.DivisionPolynomialRootCriterion.exists_coordinates_of_ne_zero W ((2 : ℕ) • P) htwo_ne
  obtain ⟨x₃, y₃, hP₃, htriple⟩ :=
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.DivisionPolynomialRootCriterion.exists_coordinates_of_ne_zero W ((3 : ℕ) • P) hthree_ne
  obtain ⟨x₄, y₄, hP₄, hfour⟩ :=
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.DivisionPolynomialRootCriterion.exists_coordinates_of_ne_zero W ((4 : ℕ) • P) hfour_ne
  have hdouble₂ :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ =
        WeierstrassCurve.Affine.Point.some x₄ y₄ hP₄ := by
    rw [← hdouble, ← hfour, ← mul_nsmul]
  have hfour_neg_three :
      (4 : ℕ) • P = -((3 : ℕ) • P) := by
    apply (add_eq_zero_iff_eq_neg).mp
    have hsplit :
        (7 : ℕ) • P = (4 : ℕ) • P + (3 : ℕ) • P := by
      rw [show (7 : ℕ) = 4 + 3 by norm_num, add_nsmul]
    rw [← hsplit]
    exact hseven
  have hx₄₃ : x₄ = x₃ := by
    have heq :
        WeierstrassCurve.Affine.Point.some x₄ y₄ hP₄ =
          -WeierstrassCurve.Affine.Point.some x₃ y₃ hP₃ := by
      rw [← hfour, ← htriple]
      exact hfour_neg_three
    exact (WeierstrassCurve.Affine.Point.some.inj heq).1
  have hcoordinate₃ :=
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.DivisionPolynomialRootCriterion.triple_abscissa_formula W hP hP₂ hP₃ hdouble htriple
  have hcoordinate₄ :=
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.DivisionPolynomialRootCriterion.quadruple_abscissa_formula W hP hP₂ hP₄ hdouble hdouble₂
  have hleft :
      Polynomial.eval x (W.Φ 4) *
            Polynomial.eval x (W.ΨSq 3) -
          Polynomial.eval x (W.Φ 3) *
            Polynomial.eval x (W.ΨSq 4) = 0 := by
    rw [hcoordinate₄, hcoordinate₃, hx₄₃]
    ring
  have hcross := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.DivisionPolynomialRootCriterion.seven_cross_identity W x
  linear_combination hcross - hleft

end MazurTorsion.DivisionPolynomialRootCriterion

end MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers

namespace MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers
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
    refine MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.some_eq_some W ?_ ?_
    · simp only [WeierstrassCurve.Affine.addX, hslope, ha₂]
      ring
    · simp only [WeierstrassCurve.Affine.negAddY,
        WeierstrassCurve.Affine.addX, hslope, ha₂]
      ring
  rw [hdouble, neg_add_cancel]



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
  exact MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.some_eq_some W hx hy

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
  obtain ⟨h₂, hdouble⟩ := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.two_mul_origin_coordinates b c hb h00
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
  exact MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.some_eq_some W hx hy

/-- In scalar-multiplication notation, `2P = (b,bc)` for the marked Tate point. -/
theorem two_nsmul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₂ : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular b (b * c),
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some b (b * c) h₂ := by
  simpa [two_nsmul] using MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.two_mul_origin_coordinates b c hb h00

/-- In scalar-multiplication notation, `3P = (c,b-c)` for the marked Tate point. -/
theorem three_nsmul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₃ : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular c (b - c),
      (3 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some c (b - c) h₃ := by
  obtain ⟨h₃, htriple⟩ := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.three_mul_origin_coordinates b c hb h00
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
  obtain ⟨h₃, htriple⟩ := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.three_mul_origin_coordinates b c hb h00
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
  exact MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.some_eq_some W hx hy


end MazurTorsion.Kubert

namespace MazurTorsion.ExceptionalTwoTen



end MazurTorsion.ExceptionalTwoTen

end
end MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers

namespace MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers
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
  obtain ⟨h₃, htriple⟩ := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.three_nsmul_origin_coordinates b c hb h00
  have hc : c ≠ 0 := by
    intro hc0
    subst hc0
    have h3eq : (3 : ℕ) • P = -P := by
      rw [htriple, hPdef, WeierstrassCurve.Affine.Point.neg_some]
      exact MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.some_eq_some _ rfl
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
  obtain ⟨h₄, hquad⟩ := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.four_mul_origin_coordinates b c hb hc h00
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
    exact (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.three_nsmul_origin_coordinates b c hb h00).choose_spec
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



/-- The invariant `c₄` of the parametrized order-seven family. -/
theorem orderSeven_c₄ (d : ℚ) :
    (MazurTorsion.Kubert.tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).c₄ =
      (d ^ 2 - d + 1) *
        (d ^ 6 - 11 * d ^ 5 + 30 * d ^ 4 - 15 * d ^ 3 -
          10 * d ^ 2 + 5 * d + 1) := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    MazurTorsion.Kubert.tateNormalCurve]
  ring

/-- The cleared `j`-identity for the order-seven hauptmodul value on the
parametrized family: with `t₇ = 49d(d-1)/(d³-8d²+5d+1)`,

`(t₇²+13t₇+49)(t₇²+245t₇+2401)³ · Δ = c₄³ · t₇⁷`. -/
theorem orderSeven_hauptmodul_identity
    (d : ℚ) (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hK : d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0) :
    ((49 * d * (d - 1) / (d ^ 3 - 8 * d ^ 2 + 5 * d + 1)) ^ 2 +
          13 * (49 * d * (d - 1) / (d ^ 3 - 8 * d ^ 2 + 5 * d + 1)) + 49) *
        ((49 * d * (d - 1) / (d ^ 3 - 8 * d ^ 2 + 5 * d + 1)) ^ 2 +
          245 * (49 * d * (d - 1) / (d ^ 3 - 8 * d ^ 2 + 5 * d + 1)) +
          2401) ^ 3 *
        (MazurTorsion.Kubert.tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ =
      (MazurTorsion.Kubert.tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).c₄ ^ 3 *
        (49 * d * (d - 1) / (d ^ 3 - 8 * d ^ 2 + 5 * d + 1)) ^ 7 := by
  rw [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSeven_Δ, MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSeven_c₄]
  set K : ℚ := d ^ 3 - 8 * d ^ 2 + 5 * d + 1 with hKdef
  field_simp [hK]
  simp only [hKdef]
  ring

end MazurTorsion.Kubert

end
end MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers

namespace MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



section
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert



/-- The explicit Tate-normalization formula at an affine point of exact
order seven is noncuspidal and satisfies the cleared level-seven
Hauptmodul identity. -/
theorem orderSevenHauptmodulAt_spec
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    {X Y : ℚ} (hns : W.toAffine.Nonsingular X Y)
    (horder : addOrderOf
      (WeierstrassCurve.Affine.Point.some X Y hns :
        W.toAffine.Point) = 7) :
    MazurTorsion.Kubert.orderSevenHauptmodulAt W X Y ≠ 0 ∧
      MazurTorsion.Kubert.orderSevenJNumerator (MazurTorsion.Kubert.orderSevenHauptmodulAt W X Y) * W.Δ =
        W.c₄ ^ 3 * MazurTorsion.Kubert.orderSevenHauptmodulAt W X Y ^ 7 := by
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some X Y hns
  have hnot : ∀ n : ℕ, ¬(7 ∣ n) → (n : ℕ) • P ≠ 0 := by
    intro n hn hzero
    exact hn (horder ▸ addOrderOf_dvd_of_nsmul_eq_zero hzero)
  have hP2 : P + P ≠ 0 := by
    intro h
    exact hnot 2 (by norm_num) (by simpa [two_nsmul] using h)
  have hP3 : P + P + P ≠ 0 := by
    intro h
    exact hnot 3 (by norm_num) (by
      rw [show (3 : ℕ) • P = P + P + P by abel]
      exact h)
  have hnotvertical : Y ≠ W.toAffine.negY X Y := fun h ↦
    hP2 (by
      dsimp only [P]
      exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq h)
  have hbeta : MazurTorsion.Kubert.pointTateBeta W X Y ≠ 0 := by
    intro h
    apply hnotvertical
    rw [WeierstrassCurve.Affine.negY]
    unfold MazurTorsion.Kubert.pointTateBeta at h
    linarith
  have htangentDenom : W.a₃ + X * W.a₁ + 2 * Y ≠ 0 := by
    simpa only [MazurTorsion.Kubert.pointTateBeta] using hbeta
  set lambda : ℚ :=
    (W.a₄ + 2 * X * W.a₂ - Y * W.a₁ + 3 * X ^ 2) /
      (W.a₃ + X * W.a₁ + 2 * Y) with hlambda
  have hlambdaPoint : lambda = MazurTorsion.Kubert.pointTateLambda W X Y := by
    rw [hlambda]
    rfl
  set C₁ : WeierstrassCurve.VariableChange ℚ := ⟨1, X, lambda, Y⟩ with hC₁
  have hC₁a₃ : (C₁ • W).a₃ = MazurTorsion.Kubert.pointTateBeta W X Y := by
    rw [WeierstrassCurve.variableChange_a₃, hC₁]
    simp [MazurTorsion.Kubert.pointTateBeta]
  have hC₁a₄ : (C₁ • W).a₄ = 0 := by
    rw [WeierstrassCurve.variableChange_a₄, hC₁]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    rw [hlambda]
    field_simp [htangentDenom]
    ring
  have hC₁a₆ : (C₁ • W).a₆ = 0 := by
    have heq := hns.1
    rw [WeierstrassCurve.Affine.equation_iff] at heq
    rw [WeierstrassCurve.variableChange_a₆, hC₁]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    linear_combination -heq
  have hC₁a₂ :
      (C₁ • W).a₂ = MazurTorsion.Kubert.pointTateAlpha W X Y := by
    rw [WeierstrassCurve.variableChange_a₂, hC₁]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    simp only [MazurTorsion.Kubert.pointTateAlpha]
    rw [← hlambdaPoint]
    ring
  have h00₁ : (C₁ • W).toAffine.Nonsingular 0 0 :=
    WeierstrassCurve.Affine.nonsingular_zero.mpr
      ⟨hC₁a₆, Or.inl (by rw [hC₁a₃]; exact hbeta)⟩
  have hmap₁ :
      MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.equivVariableChange W C₁
          (WeierstrassCurve.Affine.Point.some 0 0 h00₁) = P := by
    rw [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.equivVariableChange_some]
    dsimp only [P]
    exact MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.some_eq_some W
      (by simp [C₁]) (by simp [C₁])
  have halpha : MazurTorsion.Kubert.pointTateAlpha W X Y ≠ 0 := by
    rw [← hC₁a₂]
    intro hzero
    apply hP3
    have htriple :
        WeierstrassCurve.Affine.Point.some 0 0 h00₁ +
            WeierstrassCurve.Affine.Point.some 0 0 h00₁ +
            WeierstrassCurve.Affine.Point.some 0 0 h00₁ = 0 :=
      MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.three_nsmul_origin_eq_zero (C₁ • W) hzero hC₁a₄
        (by rw [hC₁a₃]; exact hbeta) h00₁
    have himage :=
      congrArg (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.equivVariableChange W C₁)
        htriple
    rwa [map_add, map_add, map_zero, hmap₁] at himage
  let scale : ℚˣ := Units.mk0
    (MazurTorsion.Kubert.pointTateBeta W X Y / MazurTorsion.Kubert.pointTateAlpha W X Y)
    (div_ne_zero hbeta halpha)
  let C₂ : WeierstrassCurve.VariableChange ℚ := ⟨scale, 0, 0, 0⟩
  have hscale : (scale : ℚ) =
      MazurTorsion.Kubert.pointTateBeta W X Y / MazurTorsion.Kubert.pointTateAlpha W X Y := rfl
  have hscale0 : (scale : ℚ) ≠ 0 := scale.ne_zero
  let b : ℚ := -(C₂ • (C₁ • W)).a₂
  let c : ℚ := 1 - (C₂ • (C₁ • W)).a₁
  have hC₂a₄ : (C₂ • (C₁ • W)).a₄ = 0 := by
    rw [WeierstrassCurve.variableChange_a₄]
    simp [C₂, hC₁a₄]
  have hC₂a₆ : (C₂ • (C₁ • W)).a₆ = 0 := by
    rw [WeierstrassCurve.variableChange_a₆]
    simp [C₂, hC₁a₆]
  have hC₂a₂a₃ :
      (C₂ • (C₁ • W)).a₃ = (C₂ • (C₁ • W)).a₂ := by
    rw [WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.variableChange_a₂]
    simp only [C₂, Units.val_inv_eq_inv_val]
    rw [hC₁a₃, hC₁a₂, hscale]
    field_simp [hbeta, halpha]
    ring
  have hC₂a₂ :
      (C₂ • (C₁ • W)).a₂ =
        ((scale : ℚ))⁻¹ ^ 2 * (C₁ • W).a₂ := by
    rw [WeierstrassCurve.variableChange_a₂]
    simp [C₂]
  have hC₂a₂ne : (C₂ • (C₁ • W)).a₂ ≠ 0 := by
    rw [hC₂a₂, hC₁a₂]
    exact mul_ne_zero (pow_ne_zero 2 (inv_ne_zero hscale0)) halpha
  have hb0 : b ≠ 0 := by
    dsimp only [b]
    exact neg_ne_zero.mpr hC₂a₂ne
  have hcurve : C₂ • (C₁ • W) = MazurTorsion.Kubert.tateNormalCurve b c := by
    ext <;> simp [MazurTorsion.Kubert.tateNormalCurve, b, c, hC₂a₄, hC₂a₆,
      hC₂a₂a₃]
  have h00₂ : (C₂ • (C₁ • W)).toAffine.Nonsingular 0 0 :=
    WeierstrassCurve.Affine.nonsingular_zero.mpr
      ⟨hC₂a₆, Or.inl (by rw [hC₂a₂a₃]; exact hC₂a₂ne)⟩
  let h00 : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular 0 0 :=
    hcurve ▸ h00₂
  let e : W.toAffine.Point ≃+ (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Point :=
    (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm.trans
      ((MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.equivVariableChange (C₁ • W) C₂).symm.trans
        (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.equivOfEq hcurve))
  have heP : e P = WeierstrassCurve.Affine.Point.some 0 0 h00 := by
    have hfirst :
        (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm P =
          WeierstrassCurve.Affine.Point.some 0 0 h00₁ := by
      rw [← hmap₁]
      exact (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm_apply_apply _
    have hsecond :
        MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.equivVariableChange (C₁ • W) C₂
            (WeierstrassCurve.Affine.Point.some 0 0 h00₂) =
          WeierstrassCurve.Affine.Point.some 0 0 h00₁ := by
      rw [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.equivVariableChange_some]
      exact MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.some_eq_some _
        (by simp [C₂]) (by simp [C₂])
    simp only [e, AddEquiv.trans_apply, hfirst, ← hsecond,
      AddEquiv.symm_apply_apply, MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.WeierstrassCurve.Affine.Point.equivOfEq_some]
  have h7P : (7 : ℕ) • P = 0 := by
    rw [← horder]
    exact addOrderOf_nsmul_eq_zero P
  have h7origin :
      (7 : ℕ) • (WeierstrassCurve.Affine.Point.some 0 0 h00 :
        (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Point) = 0 := by
    rw [← heP, ← map_nsmul, h7P, map_zero]
  obtain ⟨hc0, hrel⟩ := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSeven_tate_relation b c hb0 h00
    (WeierstrassCurve.Affine.Point.some_ne_zero h00) h7origin
  obtain ⟨d, hd0, hd1, hbeq, hceq⟩ :=
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSeven_parametrization b c hb0 hc0 hrel
  have hbdc : b = d * c := by
    rw [hbeq, hceq]
    ring
  have hd_ratio : d = b / c := by
    exact (eq_div_iff hc0).mpr hbdc.symm
  have hb_formula :
      b = -MazurTorsion.Kubert.pointTateAlpha W X Y ^ 3 / MazurTorsion.Kubert.pointTateBeta W X Y ^ 2 := by
    dsimp only [b]
    rw [hC₂a₂, hC₁a₂, hscale]
    field_simp [hbeta, halpha]
  have hc_formula :
      c = (MazurTorsion.Kubert.pointTateBeta W X Y - MazurTorsion.Kubert.pointTateAlpha W X Y *
          (W.a₁ + 2 * MazurTorsion.Kubert.pointTateLambda W X Y)) /
        MazurTorsion.Kubert.pointTateBeta W X Y := by
    dsimp only [c]
    rw [WeierstrassCurve.variableChange_a₁]
    simp only [C₂, Units.val_inv_eq_inv_val]
    rw [WeierstrassCurve.variableChange_a₁]
    simp only [C₁, inv_one, Units.val_one, one_mul]
    rw [hlambdaPoint]
    rw [hscale]
    field_simp [hbeta, halpha]
    ring
  have hgamma :
      MazurTorsion.Kubert.pointTateBeta W X Y - MazurTorsion.Kubert.pointTateAlpha W X Y *
          (W.a₁ + 2 * MazurTorsion.Kubert.pointTateLambda W X Y) ≠ 0 := by
    intro hzero
    apply hc0
    rw [hc_formula, hzero]
    simp
  have hratio : b / c = MazurTorsion.Kubert.pointTateParameter W X Y := by
    rw [hb_formula, hc_formula]
    simp only [MazurTorsion.Kubert.pointTateParameter]
    field_simp [hbeta, hgamma]
  have hdpoint : d = MazurTorsion.Kubert.pointTateParameter W X Y :=
    hd_ratio.trans hratio
  have hdisc :
      ((scale : ℚ))⁻¹ ^ 12 * W.Δ = (MazurTorsion.Kubert.tateNormalCurve b c).Δ := by
    rw [← hcurve, WeierstrassCurve.variableChange_Δ,
      WeierstrassCurve.variableChange_Δ]
    simp [C₁, C₂]
  have hc₄ :
      ((scale : ℚ))⁻¹ ^ 4 * W.c₄ = (MazurTorsion.Kubert.tateNormalCurve b c).c₄ := by
    rw [← hcurve, WeierstrassCurve.variableChange_c₄,
      WeierstrassCurve.variableChange_c₄]
    simp [C₁, C₂]
  have hK : d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0 := by
    intro hK0
    have hΔzero : (MazurTorsion.Kubert.tateNormalCurve b c).Δ = 0 := by
      rw [hbeq, hceq, MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSeven_Δ, hK0]
      ring
    have hΔne : (MazurTorsion.Kubert.tateNormalCurve b c).Δ ≠ 0 := by
      rw [← hdisc]
      exact mul_ne_zero (pow_ne_zero 12 (inv_ne_zero hscale0))
        W.isUnit_Δ.ne_zero
    exact hΔne hΔzero
  let B : ℚ := 49 * d * (d - 1) /
    (d ^ 3 - 8 * d ^ 2 + 5 * d + 1)
  have hBat : MazurTorsion.Kubert.orderSevenHauptmodulAt W X Y = B := by
    simp only [MazurTorsion.Kubert.orderSevenHauptmodulAt]
    rw [← hdpoint]
  rw [hBat]
  have hB0 : B ≠ 0 := by
    dsimp only [B]
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) hd0)
        (sub_ne_zero.mpr hd1)) hK
  refine ⟨hB0, ?_⟩
  have hfam := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSeven_hauptmodul_identity d hd0 hd1 hK
  apply mul_left_cancel₀ (pow_ne_zero 12 (inv_ne_zero hscale0))
  calc
    ((scale : ℚ))⁻¹ ^ 12 * (MazurTorsion.Kubert.orderSevenJNumerator B * W.Δ) =
        MazurTorsion.Kubert.orderSevenJNumerator B * (((scale : ℚ))⁻¹ ^ 12 * W.Δ) := by ring
    _ = MazurTorsion.Kubert.orderSevenJNumerator B * (MazurTorsion.Kubert.tateNormalCurve b c).Δ := by
      rw [hdisc]
    _ = MazurTorsion.Kubert.orderSevenJNumerator B *
        (MazurTorsion.Kubert.tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ := by
      rw [hbeq, hceq]
    _ = (MazurTorsion.Kubert.tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).c₄ ^ 3 * B ^ 7 := by
      dsimp only [B, MazurTorsion.Kubert.orderSevenJNumerator]
      exact hfam
    _ = (MazurTorsion.Kubert.tateNormalCurve b c).c₄ ^ 3 * B ^ 7 := by
      rw [hbeq, hceq]
    _ = (((scale : ℚ))⁻¹ ^ 4 * W.c₄) ^ 3 * B ^ 7 := by
      rw [hc₄]
    _ = ((scale : ℚ))⁻¹ ^ 12 * (W.c₄ ^ 3 * B ^ 7) := by ring



end MazurTorsion.Kubert

end
end MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers

namespace MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/




open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert













/-- The `c₄` invariant of the marked order-seven quotient model. -/
theorem orderSevenQuotient_c₄ (d : ℚ) :
    (MazurTorsion.Kubert.orderSevenQuotient d).c₄ =
      (d ^ 2 - d + 1) *
        (d ^ 6 + 229 * d ^ 5 + 270 * d ^ 4 - 1695 * d ^ 3 +
          1430 * d ^ 2 - 235 * d + 1) := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, MazurTorsion.Kubert.orderSevenQuotient,
    MazurTorsion.Kubert.orderSevenB, MazurTorsion.Kubert.orderSevenC]
  ring



/-- The quotient invariants satisfy the level-seven Hauptmodul identity
for the Fricke/backtracking parameter. -/
theorem orderSevenQuotient_hauptmodul_identity
    (d : ℚ) (hd0 : d ≠ 0) (hd1 : d ≠ 1) :
    MazurTorsion.Kubert.orderSevenJNumerator (MazurTorsion.Kubert.orderSevenFrickeParameter d) *
        (MazurTorsion.Kubert.orderSevenQuotient d).Δ =
      (MazurTorsion.Kubert.orderSevenQuotient d).c₄ ^ 3 *
        MazurTorsion.Kubert.orderSevenFrickeParameter d ^ 7 := by
  rw [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenQuotient_Δ, MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenQuotient_c₄]
  simp only [MazurTorsion.Kubert.orderSevenJNumerator, MazurTorsion.Kubert.orderSevenFrickeParameter]
  field_simp [hd0, sub_ne_zero.mpr hd1]
  ring






























































/-- The Fricke/backtracking Hauptmodul is nonzero on every nonsingular
member of the source family. -/
theorem orderSevenFrickeParameter_ne_zero
    (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    MazurTorsion.Kubert.orderSevenFrickeParameter d ≠ 0 := by
  obtain ⟨hd0, hd1, hK⟩ := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenFamily_parameters_ne d
  exact div_ne_zero hK
    (mul_ne_zero hd0 (sub_ne_zero.mpr hd1))

private theorem orderSevenB_ne_zero
    (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    MazurTorsion.Kubert.orderSevenB d ≠ 0 := by
  obtain ⟨hd0, hd1, -⟩ := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenFamily_parameters_ne d
  rw [show MazurTorsion.Kubert.orderSevenB d = d ^ 2 * (d - 1) by
    simp only [MazurTorsion.Kubert.orderSevenB]
    ring]
  exact mul_ne_zero (pow_ne_zero 2 hd0) (sub_ne_zero.mpr hd1)























private theorem seven_nsmul_of_kernelX
    {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hx : MazurTorsion.Kubert.OrderSevenKernelX d x) :
    (7 : ℕ) •
        (WeierstrassCurve.Affine.Point.some x y hP :
          (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 0 := by
  let P : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point := MazurTorsion.Kubert.orderSevenOrigin d
  have hb : MazurTorsion.Kubert.orderSevenB d ≠ 0 := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenB_ne_zero d
  have h00 := MazurTorsion.Kubert.orderSevenOrigin_nonsingular d
  obtain ⟨h₂, htwo⟩ :=
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.two_nsmul_origin_coordinates (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) hb h00
  obtain ⟨h₃, hthree⟩ :=
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.three_nsmul_origin_coordinates (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) hb h00
  have hseven : (7 : ℕ) • P = 0 := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.seven_nsmul_orderSevenOrigin d
  have hmultiple (n : ℕ) : (7 : ℕ) • (n • P) = 0 := by
    calc
      (7 : ℕ) • (n • P) = n • ((7 : ℕ) • P) := by
        simp only [← mul_nsmul, Nat.mul_comm]
      _ = 0 := by rw [hseven]; simp
  have hnegative {Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
      (hQ : (7 : ℕ) • Q = 0) : (7 : ℕ) • (-Q) = 0 := by
    rw [neg_nsmul, hQ, neg_zero]
  rcases hx with hx0 | hxb | hxc
  · have hxiff :
        (WeierstrassCurve.Affine.Point.some x y hP =
            WeierstrassCurve.Affine.Point.some 0 0 h00 ∨
          WeierstrassCurve.Affine.Point.some x y hP =
            -WeierstrassCurve.Affine.Point.some 0 0 h00) :=
      (WeierstrassCurve.Affine.Point.X_eq_iff
        (W := (MazurTorsion.Kubert.orderSevenFamily d).toAffine)).mp hx0
    rcases hxiff with h | h
    · rw [h]
      exact hseven
    · rw [h]
      exact hnegative hseven
  · have hxiff :
        (WeierstrassCurve.Affine.Point.some x y hP =
            WeierstrassCurve.Affine.Point.some
              (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenB d * MazurTorsion.Kubert.orderSevenC d) h₂ ∨
          WeierstrassCurve.Affine.Point.some x y hP =
            -WeierstrassCurve.Affine.Point.some
              (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenB d * MazurTorsion.Kubert.orderSevenC d) h₂) :=
      (WeierstrassCurve.Affine.Point.X_eq_iff
        (W := (MazurTorsion.Kubert.orderSevenFamily d).toAffine)).mp hxb
    rcases hxiff with h | h
    · rw [h, ← htwo]
      exact hmultiple 2
    · rw [h, ← htwo]
      exact hnegative (hmultiple 2)
  · have hxiff :
        (WeierstrassCurve.Affine.Point.some x y hP =
            WeierstrassCurve.Affine.Point.some
              (MazurTorsion.Kubert.orderSevenC d) (MazurTorsion.Kubert.orderSevenB d - MazurTorsion.Kubert.orderSevenC d) h₃ ∨
          WeierstrassCurve.Affine.Point.some x y hP =
            -WeierstrassCurve.Affine.Point.some
              (MazurTorsion.Kubert.orderSevenC d) (MazurTorsion.Kubert.orderSevenB d - MazurTorsion.Kubert.orderSevenC d) h₃) :=
      (WeierstrassCurve.Affine.Point.X_eq_iff
        (W := (MazurTorsion.Kubert.orderSevenFamily d).toAffine)).mp hxc
    rcases hxiff with h | h
    · rw [h, ← hthree]
      exact hmultiple 3
    · rw [h, ← hthree]
      exact hnegative (hmultiple 3)













/-- An affine point of exact order `49` cannot lie in the marked
order-seven kernel. -/
theorem not_orderSevenKernelX_of_order_fortyNine
    {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (horder : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49) :
    ¬MazurTorsion.Kubert.OrderSevenKernelX d x := by
  intro hx
  have hzero : MazurTorsion.Kubert.orderSevenPointMap d
      (WeierstrassCurve.Affine.Point.some x y hP) = 0 :=
    (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenPointMap_some_eq_zero_iff hP).2 hx
  have hkilled := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenPointMap_kernel_killed_by_seven hzero
  have hdvd : (49 : ℕ) ∣ 7 := by
    rw [← horder]
    exact addOrderOf_dvd_of_nsmul_eq_zero hkilled
  norm_num at hdvd





/-- For an affine order-`49` point, the residual Hauptmodul is the explicit
Tate-normalization expression evaluated at its Vélu image. -/
theorem orderSevenResidualHauptmodul_spec_of_order_fortyNine
    {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hQ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d
      ((7 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP) = 0)
    (hmap : MazurTorsion.Kubert.orderSevenPointMap d
      ((7 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP) =
        (7 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d
          (WeierstrassCurve.Affine.Point.some x y hP)) :
    MazurTorsion.Kubert.orderSevenResidualHauptmodul d x y ≠ 0 ∧
      MazurTorsion.Kubert.orderSevenJNumerator (MazurTorsion.Kubert.orderSevenResidualHauptmodul d x y) *
          (MazurTorsion.Kubert.orderSevenQuotient d).Δ =
        (MazurTorsion.Kubert.orderSevenQuotient d).c₄ ^ 3 *
          MazurTorsion.Kubert.orderSevenResidualHauptmodul d x y ^ 7 := by
  have hx : ¬MazurTorsion.Kubert.OrderSevenKernelX d x := by
    intro hx
    have hkilled := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.seven_nsmul_of_kernelX hP hx
    have hdvd : (49 : ℕ) ∣ 7 := by
      rw [← hQ]
      exact addOrderOf_dvd_of_nsmul_eq_zero hkilled
    norm_num at hdvd
  have hx0 : x ≠ 0 := fun h ↦ hx (Or.inl h)
  have hxb : x ≠ MazurTorsion.Kubert.orderSevenB d :=
    fun h ↦ hx (Or.inr (Or.inl h))
  have hxc : x ≠ MazurTorsion.Kubert.orderSevenC d :=
    fun h ↦ hx (Or.inr (Or.inr h))
  have horderImage :=
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.addOrderOf_orderSevenPointMap_of_order_fortyNine hQ hkernel hmap
  have horderVelu :
      addOrderOf (MazurTorsion.Kubert.orderSevenVeluPoint hP hx0 hxb hxc) = 7 := by
    rw [← MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenPointMap_some_of_not_kernelX hP hx]
    exact horderImage
  have hspec := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenHauptmodulAt_spec
    (MazurTorsion.Kubert.orderSevenQuotient d)
    ((MazurTorsion.Kubert.orderSevenQuotient d).toAffine.equation_iff_nonsingular.mp
      (MazurTorsion.Kubert.orderSevenVelu_equation hP.1 hx0 hxb hxc))
    (by simpa only [MazurTorsion.Kubert.orderSevenVeluPoint] using horderVelu)
  simpa only [MazurTorsion.Kubert.orderSevenResidualHauptmodul] using hspec

/-- A second nonbacktracking level-seven Hauptmodul for the quotient gives
a point on the level-`49` correspondence.  This packages the cancellation
of the nonzero quotient discriminant; constructing `B` and proving that it
differs from the Fricke/backtracking parameter remain separate tasks. -/
theorem orderSevenG7F_eq_zero_of_quotient_hauptmodul
    {d B : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hoff : MazurTorsion.Kubert.orderSevenFrickeParameter d ≠ B)
    (hB : MazurTorsion.Kubert.orderSevenJNumerator B * (MazurTorsion.Kubert.orderSevenQuotient d).Δ =
      (MazurTorsion.Kubert.orderSevenQuotient d).c₄ ^ 3 * B ^ 7) :
    MazurTorsion.Kubert.orderSevenG7F (MazurTorsion.Kubert.orderSevenFrickeParameter d) B = 0 := by
  apply (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenG7F_eq_zero_iff_crossMultiply hoff).mpr
  obtain ⟨hd0, hd1, -⟩ := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenFamily_parameters_ne d
  have hs := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenQuotient_hauptmodul_identity d hd0 hd1
  apply mul_left_cancel₀ (MazurTorsion.Kubert.orderSevenQuotient d).isUnit_Δ.ne_zero
  calc
    (MazurTorsion.Kubert.orderSevenQuotient d).Δ *
          (MazurTorsion.Kubert.orderSevenJNumerator (MazurTorsion.Kubert.orderSevenFrickeParameter d) * B ^ 7) =
        (MazurTorsion.Kubert.orderSevenJNumerator (MazurTorsion.Kubert.orderSevenFrickeParameter d) *
          (MazurTorsion.Kubert.orderSevenQuotient d).Δ) * B ^ 7 := by ring
    _ = ((MazurTorsion.Kubert.orderSevenQuotient d).c₄ ^ 3 *
          MazurTorsion.Kubert.orderSevenFrickeParameter d ^ 7) * B ^ 7 := by rw [hs]
    _ = ((MazurTorsion.Kubert.orderSevenQuotient d).c₄ ^ 3 * B ^ 7) *
          MazurTorsion.Kubert.orderSevenFrickeParameter d ^ 7 := by ring
    _ = (MazurTorsion.Kubert.orderSevenJNumerator B * (MazurTorsion.Kubert.orderSevenQuotient d).Δ) *
          MazurTorsion.Kubert.orderSevenFrickeParameter d ^ 7 := by rw [hB]
    _ = (MazurTorsion.Kubert.orderSevenQuotient d).Δ *
          (MazurTorsion.Kubert.orderSevenJNumerator B *
            MazurTorsion.Kubert.orderSevenFrickeParameter d ^ 7) := by ring

/-- The explicit residual Hauptmodul attached to an affine order-`49`
point lies on the level-`49` correspondence whenever it is not the
Fricke/backtracking parameter. -/
theorem orderSevenG7F_residual_eq_zero_of_order_fortyNine
    {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hQ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d
      ((7 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP) = 0)
    (hmap : MazurTorsion.Kubert.orderSevenPointMap d
      ((7 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP) =
        (7 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d
          (WeierstrassCurve.Affine.Point.some x y hP))
    (hoff : MazurTorsion.Kubert.orderSevenFrickeParameter d ≠
      MazurTorsion.Kubert.orderSevenResidualHauptmodul d x y) :
    MazurTorsion.Kubert.orderSevenG7F (MazurTorsion.Kubert.orderSevenFrickeParameter d)
        (MazurTorsion.Kubert.orderSevenResidualHauptmodul d x y) = 0 := by
  apply MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenG7F_eq_zero_of_quotient_hauptmodul hoff
  exact (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenResidualHauptmodul_spec_of_order_fortyNine
    hP hQ hkernel hmap).2

end MazurTorsion.Kubert

end MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers

namespace MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



section
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The raw cross-multiplied equation saying that the quotient point's
level-seven Hauptmodul is the Fricke partner of the source parameter. -/
def orderSevenRawSelectionNumerator (d X Y : ℚ) : ℚ :=
  let W := MazurTorsion.Kubert.orderSevenQuotient d
  let A := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateParameterClearedNumerator W X Y
  let B := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateParameterClearedDenominator W X Y
  d * (d - 1) * MazurTorsion.Kubert.orderSevenParameterHauptmodulNumerator A B -
    (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) *
      MazurTorsion.Kubert.orderSevenParameterCubic A B

/-- Equality with the Fricke parameter forces the raw cleared selection
equation. -/
theorem orderSevenRawSelectionNumerator_eq_zero_of_hauptmodul_eq_fricke
    {d X Y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (h : MazurTorsion.Kubert.orderSevenHauptmodulAt (MazurTorsion.Kubert.orderSevenQuotient d) X Y =
      MazurTorsion.Kubert.orderSevenFrickeParameter d) :
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenRawSelectionNumerator d X Y = 0 := by
  have hhaupt :
      MazurTorsion.Kubert.orderSevenHauptmodulAt (MazurTorsion.Kubert.orderSevenQuotient d) X Y ≠ 0 := by
    rw [h]
    exact MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenFrickeParameter_ne_zero d
  have hbeta : MazurTorsion.Kubert.pointTateBeta (MazurTorsion.Kubert.orderSevenQuotient d) X Y ≠ 0 :=
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateBeta_ne_zero_of_hauptmodul_ne_zero _ hhaupt
  rw [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenHauptmodulAt_eq_cleared _ hbeta] at h
  let A := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateParameterClearedNumerator (MazurTorsion.Kubert.orderSevenQuotient d) X Y
  let B := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateParameterClearedDenominator (MazurTorsion.Kubert.orderSevenQuotient d) X Y
  let C := MazurTorsion.Kubert.orderSevenParameterCubic A B
  let N := MazurTorsion.Kubert.orderSevenParameterHauptmodulNumerator A B
  have hfrac : N / C =
      (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) / (d * (d - 1)) := by
    simpa only [A, B, C, N, MazurTorsion.Kubert.orderSevenFrickeParameter] using h
  have hC : C ≠ 0 := by
    intro hC
    have : N / C = 0 := by simp [hC]
    rw [this] at hfrac
    exact MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenFrickeParameter_ne_zero d hfrac.symm
  obtain ⟨hd0, hd1, -⟩ := MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenFamily_parameters_ne d
  have hdd : d * (d - 1) ≠ 0 :=
    mul_ne_zero hd0 (sub_ne_zero.mpr hd1)
  simp only [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenRawSelectionNumerator]
  change d * (d - 1) * N -
    (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) * C = 0
  apply sub_eq_zero.mpr
  simpa only [mul_comm] using (div_eq_div_iff hC hdd).mp hfrac











private theorem pointTateCompletedTangentNumerator_eq
    (W : WeierstrassCurve ℚ) (x y : ℚ) :
    MazurTorsion.Kubert.pointTateCompletedTangentNumerator W x =
      W.a₁ * MazurTorsion.Kubert.pointTateBeta W x y +
        2 * MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateLambdaNumerator W x y := by
  simp only [MazurTorsion.Kubert.pointTateCompletedTangentNumerator, MazurTorsion.Kubert.pointTateBeta,
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateLambdaNumerator, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄]
  ring

private theorem completedCubic_eq_pointTateBeta_sq
    (W : WeierstrassCurve ℚ) {x y : ℚ}
    (hcurve : W.toAffine.Equation x y) :
    MazurTorsion.Doubling.completedCubic W x = MazurTorsion.Kubert.pointTateBeta W x y ^ 2 := by
  rw [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Doubling.completedCubic_eq_completedY_sq W hcurve]
  simp only [MazurTorsion.Kubert.pointTateBeta]
  congr 1
  ring

private theorem pointTateAlphaUnivariateCleared_eq
    (W : WeierstrassCurve ℚ) {x y : ℚ}
    (hcurve : W.toAffine.Equation x y) :
    MazurTorsion.Kubert.pointTateAlphaUnivariateCleared W x =
      4 * MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateAlphaCleared W x y := by
  rw [MazurTorsion.Kubert.pointTateAlphaUnivariateCleared,
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.completedCubic_eq_pointTateBeta_sq W hcurve,
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateCompletedTangentNumerator_eq W x y]
  simp only [MazurTorsion.Kubert.pointTateBeta, MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateAlphaCleared,
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateLambdaNumerator, WeierstrassCurve.b₂]
  ring

private theorem pointTateGammaUnivariateCleared_eq
    (W : WeierstrassCurve ℚ) {x y : ℚ}
    (hcurve : W.toAffine.Equation x y) :
    MazurTorsion.Kubert.pointTateGammaUnivariateCleared W x =
      4 * MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateGammaCleared W x y := by
  rw [MazurTorsion.Kubert.pointTateGammaUnivariateCleared,
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.completedCubic_eq_pointTateBeta_sq W hcurve,
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateAlphaUnivariateCleared_eq W hcurve,
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateCompletedTangentNumerator_eq W x y]
  simp only [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateGammaCleared]
  ring

private theorem pointTateParameterUnivariateNumerator_eq
    (W : WeierstrassCurve ℚ) {x y : ℚ}
    (hcurve : W.toAffine.Equation x y) :
    MazurTorsion.Kubert.pointTateParameterUnivariateNumerator W x =
      64 * MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateParameterClearedNumerator W x y := by
  rw [MazurTorsion.Kubert.pointTateParameterUnivariateNumerator,
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateAlphaUnivariateCleared_eq W hcurve]
  simp only [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateParameterClearedNumerator]
  ring

private theorem pointTateParameterUnivariateDenominator_eq
    (W : WeierstrassCurve ℚ) {x y : ℚ}
    (hcurve : W.toAffine.Equation x y) :
    MazurTorsion.Kubert.pointTateParameterUnivariateDenominator W x =
      64 * MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateParameterClearedDenominator W x y := by
  rw [MazurTorsion.Kubert.pointTateParameterUnivariateDenominator,
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateGammaUnivariateCleared_eq W hcurve,
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.completedCubic_eq_pointTateBeta_sq W hcurve]
  simp only [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateParameterClearedDenominator]
  ring



/-- On the quotient curve, the abscissa-only selection polynomial is
`64 ^ 3` times the raw cleared equation. -/
theorem orderSevenSelectionPolynomial_eq_raw
    {d X Y : ℚ}
    (hcurve : (MazurTorsion.Kubert.orderSevenQuotient d).toAffine.Equation X Y) :
    MazurTorsion.Kubert.orderSevenSelectionPolynomial d X =
      64 ^ 3 * MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenRawSelectionNumerator d X Y := by
  simp only [MazurTorsion.Kubert.orderSevenSelectionPolynomial,
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenRawSelectionNumerator]
  rw [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateParameterUnivariateNumerator_eq _ hcurve,
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.pointTateParameterUnivariateDenominator_eq _ hcurve]
  simp only [MazurTorsion.Kubert.orderSevenParameterHauptmodulNumerator,
    MazurTorsion.Kubert.orderSevenParameterCubic]
  ring

/-- Fricke equality at a quotient point forces the compact selection
polynomial to vanish at its abscissa. -/
theorem orderSevenSelectionPolynomial_eq_zero_of_hauptmodul_eq_fricke
    {d X Y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hcurve : (MazurTorsion.Kubert.orderSevenQuotient d).toAffine.Equation X Y)
    (h : MazurTorsion.Kubert.orderSevenHauptmodulAt (MazurTorsion.Kubert.orderSevenQuotient d) X Y =
      MazurTorsion.Kubert.orderSevenFrickeParameter d) :
    MazurTorsion.Kubert.orderSevenSelectionPolynomial d X = 0 := by
  rw [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenSelectionPolynomial_eq_raw hcurve,
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenRawSelectionNumerator_eq_zero_of_hauptmodul_eq_fricke h]
  ring

/-- Exact order `49` keeps a source point away from the order-seven kernel,
so Fricke equality for its explicit Vélu image forces the compact selection
polynomial to vanish. -/
theorem orderSevenSelectionPolynomial_eq_zero_of_residual_eq_fricke
    {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hQ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49)
    (h : MazurTorsion.Kubert.orderSevenResidualHauptmodul d x y =
      MazurTorsion.Kubert.orderSevenFrickeParameter d) :
    MazurTorsion.Kubert.orderSevenSelectionPolynomial d (MazurTorsion.Kubert.orderSevenVeluX d x) = 0 := by
  have hx : ¬MazurTorsion.Kubert.OrderSevenKernelX d x := by
    exact MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.not_orderSevenKernelX_of_order_fortyNine hP hQ
  have hx0 : x ≠ 0 := fun hx0 ↦ hx (Or.inl hx0)
  have hxb : x ≠ MazurTorsion.Kubert.orderSevenB d :=
    fun hxb ↦ hx (Or.inr (Or.inl hxb))
  have hxc : x ≠ MazurTorsion.Kubert.orderSevenC d :=
    fun hxc ↦ hx (Or.inr (Or.inr hxc))
  apply MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenSelectionPolynomial_eq_zero_of_hauptmodul_eq_fricke
    (MazurTorsion.Kubert.orderSevenVelu_equation hP.1 hx0 hxb hxc)
  exact h

end MazurTorsion.Kubert

end
end MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers

namespace MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

































































/-- A nonbacktracking residual Hauptmodul lies on the level-`49`
correspondence from the zero-fiber hypothesis alone. -/
theorem orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_kernel
    {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hQ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d
      ((7 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP) = 0)
    (hoff : MazurTorsion.Kubert.orderSevenFrickeParameter d ≠
      MazurTorsion.Kubert.orderSevenResidualHauptmodul d x y) :
    MazurTorsion.Kubert.orderSevenG7F (MazurTorsion.Kubert.orderSevenFrickeParameter d)
        (MazurTorsion.Kubert.orderSevenResidualHauptmodul d x y) = 0 := by
  exact MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenG7F_residual_eq_zero_of_order_fortyNine
    hP hQ hkernel
      (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenPointMap_seven_nsmul_of_order_fortyNine hQ hkernel) hoff

end MazurTorsion.Kubert

end MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers

namespace MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The image on the quotient curve of an order-`49` point satisfying the
kernel condition is a root of the quotient seventh division polynomial. -/
theorem orderSevenQuotient_preΨ_seven_eval_eq_zero_of_order_fortyNine_of_kernel
    {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hQ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d
      ((7 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP) = 0) :
    ((MazurTorsion.Kubert.orderSevenQuotient d).preΨ' 7).eval (MazurTorsion.Kubert.orderSevenVeluX d x) = 0 := by
  have hx : ¬MazurTorsion.Kubert.OrderSevenKernelX d x :=
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.not_orderSevenKernelX_of_order_fortyNine hP hQ
  have hx₀ : x ≠ 0 := fun h ↦ hx (Or.inl h)
  have hxB : x ≠ MazurTorsion.Kubert.orderSevenB d :=
    fun h ↦ hx (Or.inr (Or.inl h))
  have hxC : x ≠ MazurTorsion.Kubert.orderSevenC d :=
    fun h ↦ hx (Or.inr (Or.inr h))
  let hV : (MazurTorsion.Kubert.orderSevenQuotient d).toAffine.Nonsingular
      (MazurTorsion.Kubert.orderSevenVeluX d x) (MazurTorsion.Kubert.orderSevenVeluY d x y) :=
    (MazurTorsion.Kubert.orderSevenQuotient d).toAffine.equation_iff_nonsingular.mp
      (MazurTorsion.Kubert.orderSevenVelu_equation hP.1 hx₀ hxB hxC)
  let V : (MazurTorsion.Kubert.orderSevenQuotient d).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some
      (MazurTorsion.Kubert.orderSevenVeluX d x) (MazurTorsion.Kubert.orderSevenVeluY d x y) hV
  have hmapV : MazurTorsion.Kubert.orderSevenPointMap d
      (WeierstrassCurve.Affine.Point.some x y hP) = V := by
    rw [MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenPointMap_some_of_not_kernelX hP hx]
    simp only [V, MazurTorsion.Kubert.orderSevenVeluPoint]
  have horderV : addOrderOf V = 7 := by
    rw [← hmapV]
    exact MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.addOrderOf_orderSevenPointMap_of_order_fortyNine_of_kernel
      hQ hkernel
  have hsevenV : (7 : ℕ) • V = 0 := by
    rw [← horderV]
    exact addOrderOf_nsmul_eq_zero V
  exact MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.DivisionPolynomialRootCriterion.hasDivisionPolynomialRootCriterion_seven
    (MazurTorsion.Kubert.orderSevenQuotient d) hV hsevenV

/-- If the backtracking selection polynomial and the quotient seventh
division polynomial cannot both vanish, the residual Hauptmodul is not the
Fricke parameter. -/
theorem orderSevenResidualHauptmodul_ne_fricke_of_obstruction
    {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hQ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d
      ((7 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP) = 0)
    (hobstruction :
      MazurTorsion.Kubert.orderSevenSelectionPolynomial d (MazurTorsion.Kubert.orderSevenVeluX d x) ≠ 0 ∨
        ((MazurTorsion.Kubert.orderSevenQuotient d).preΨ' 7).eval
          (MazurTorsion.Kubert.orderSevenVeluX d x) ≠ 0) :
    MazurTorsion.Kubert.orderSevenResidualHauptmodul d x y ≠ MazurTorsion.Kubert.orderSevenFrickeParameter d := by
  intro hbacktracks
  have hselection :
      MazurTorsion.Kubert.orderSevenSelectionPolynomial d (MazurTorsion.Kubert.orderSevenVeluX d x) = 0 :=
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenSelectionPolynomial_eq_zero_of_residual_eq_fricke
      hP hQ hbacktracks
  have hdivision :
      ((MazurTorsion.Kubert.orderSevenQuotient d).preΨ' 7).eval
        (MazurTorsion.Kubert.orderSevenVeluX d x) = 0 :=
    MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenQuotient_preΨ_seven_eval_eq_zero_of_order_fortyNine_of_kernel
      hP hQ hkernel
  exact hobstruction.elim (· hselection) (· hdivision)

/-- A polynomial nonvanishing obstruction supplies the missing
nonbacktracking hypothesis in the existing order-seven isogeny-tower theorem. -/
theorem orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_obstruction
    {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hQ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d
      ((7 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP) = 0)
    (hobstruction :
      MazurTorsion.Kubert.orderSevenSelectionPolynomial d (MazurTorsion.Kubert.orderSevenVeluX d x) ≠ 0 ∨
        ((MazurTorsion.Kubert.orderSevenQuotient d).preΨ' 7).eval
          (MazurTorsion.Kubert.orderSevenVeluX d x) ≠ 0) :
    MazurTorsion.Kubert.orderSevenG7F (MazurTorsion.Kubert.orderSevenFrickeParameter d)
        (MazurTorsion.Kubert.orderSevenResidualHauptmodul d x y) = 0 := by
  apply MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_kernel
    hP hQ hkernel
  exact (MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenResidualHauptmodul_ne_fricke_of_obstruction
    hP hQ hkernel hobstruction).symm

end MazurTorsion.Kubert

end MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers

theorem solution {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hQ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d
      ((7 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP) = 0)
    (hobstruction :
      MazurTorsion.Kubert.orderSevenSelectionPolynomial d (MazurTorsion.Kubert.orderSevenVeluX d x) ≠ 0 ∨
        ((MazurTorsion.Kubert.orderSevenQuotient d).preΨ' 7).eval
          (MazurTorsion.Kubert.orderSevenVeluX d x) ≠ 0) :
    MazurTorsion.Kubert.orderSevenG7F (MazurTorsion.Kubert.orderSevenFrickeParameter d)
        (MazurTorsion.Kubert.orderSevenResidualHauptmodul d x y) = 0 := by
  exact MazurTransfer.Order49ThreeOriginalG7FResultantComponentHelpers.MazurTorsion.Kubert.orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_obstruction (d := d) (x := x) (y := y) hP hQ hkernel hobstruction
#print axioms solution
