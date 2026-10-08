-- Prove2me | solution 1 for MazurTransfer.order49_residual_orderSevenResidualHauptmodul_spec_of_order_fortyNine_of_kernel
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T05:18:14.005589+00:00
-- url     : https://prove2.me/submissions/770a2485-e341-4a02-ac38-9e5d4a4e48bc

import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49HauptmodulJNumerator
import Definitions.Def_MazurTransfer_Order49MarkedOriginPoint
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
import Mathlib
import Theorems.Thm_MazurTransfer_order49_geometry_orderSeven_discriminant
import Theorems.Thm_MazurTransfer_order49_marked_origin_orderSevenFamily_parameters_ne
import Theorems.Thm_MazurTransfer_order49_marked_origin_seven_nsmul_orderSevenOrigin
import Theorems.Thm_MazurTransfer_order49_point_map_addOrderOf_orderSevenPointMap_of_order_fortyNine
import Theorems.Thm_MazurTransfer_order49_point_map_orderSevenPointMap_seven_nsmul_of_order_fortyNine
import Theorems.Thm_MazurTransfer_order49_point_map_orderSevenPointMap_some_of_not_kernelX
open Polynomial
open _root_.WeierstrassCurve
open _root_.WeierstrassCurve.Affine
open _root_.WeierstrassCurve.Affine.Point hiding neg_zero map_zero
theorem MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.addOrderOf_orderSevenPointMap_of_order_fortyNine {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d ((7 : ℕ) • Q) = 0)
    (hmap : MazurTorsion.Kubert.orderSevenPointMap d ((7 : ℕ) • Q) =
      (7 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d Q) :
    addOrderOf (MazurTorsion.Kubert.orderSevenPointMap d Q) = 7 := by
  apply MazurTransfer.order49_point_map_addOrderOf_orderSevenPointMap_of_order_fortyNine <;> assumption

theorem MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.orderSevenFamily_parameters_ne (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    d ≠ 0 ∧ d ≠ 1 ∧
      d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0 := by
  apply MazurTransfer.order49_marked_origin_orderSevenFamily_parameters_ne <;> assumption

theorem MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.orderSevenPointMap_seven_nsmul_of_order_fortyNine {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d ((7 : ℕ) • Q) = 0) :
    MazurTorsion.Kubert.orderSevenPointMap d ((7 : ℕ) • Q) =
      (7 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d Q := by
  apply MazurTransfer.order49_point_map_orderSevenPointMap_seven_nsmul_of_order_fortyNine <;> assumption

theorem MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.orderSevenPointMap_some_of_not_kernelX {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hx : ¬MazurTorsion.Kubert.OrderSevenKernelX d x) :
    MazurTorsion.Kubert.orderSevenPointMap d (.some x y hP) =
      MazurTorsion.Kubert.orderSevenVeluPoint hP
        (fun h ↦ hx (Or.inl h))
        (fun h ↦ hx (Or.inr (Or.inl h)))
        (fun h ↦ hx (Or.inr (Or.inr h))) := by
  apply MazurTransfer.order49_point_map_orderSevenPointMap_some_of_not_kernelX <;> assumption

theorem MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.orderSeven_Δ (d : ℚ) :
    (MazurTorsion.Kubert.tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ =
      d ^ 7 * (d - 1) ^ 7 * (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) := by
  apply MazurTransfer.order49_geometry_orderSeven_discriminant <;> assumption

theorem MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.seven_nsmul_orderSevenOrigin (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    (7 : ℕ) • MazurTorsion.Kubert.orderSevenOrigin d = 0 := by
  apply MazurTransfer.order49_marked_origin_seven_nsmul_orderSevenOrigin <;> assumption
namespace MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair
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
  rw [MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.variableChange_negY] at hY
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
  simp only [addY, MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.variableChange_negAddY, MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.variableChange_addX, MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.variableChange_negY]

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
      rw [MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.variableChange_negY]
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
  rw [Affine.Nonsingular, Affine.Nonsingular, MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.variableChange_equation W C,
    MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.variableChange_polynomialX W C, MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.variableChange_polynomialY W C]
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
      ((MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.variableChange_nonsingular W C x y).mpr h)

@[simp] lemma mapVariableChangeFun_zero : MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.mapVariableChangeFun W C 0 = 0 := rfl

lemma mapVariableChangeFun_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.mapVariableChangeFun W C (.some x y h)
      = .some ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
          ((MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.variableChange_nonsingular W C x y).mpr h) := rfl

lemma some_eq_some (W : WeierstrassCurve F) {x₁ x₂ y₁ y₂ : F} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : W.toAffine.Nonsingular x₁ y₁} {h₂ : W.toAffine.Nonsingular x₂ y₂} :
    (some x₁ y₁ h₁ : W.toAffine.Point) = some x₂ y₂ h₂ := by
  subst hx hy
  rfl

lemma mapVariableChangeFun_injective :
    Function.Injective (MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.mapVariableChangeFun W C) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · simp [MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.mapVariableChangeFun] at h
  · simp [MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.mapVariableChangeFun] at h
  · rw [MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.mapVariableChangeFun_some, MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.mapVariableChangeFun_some] at h
    injection h with hX hY
    have hx : x₁ = x₂ := mul_left_cancel₀ (pow_ne_zero 2 hu) (by linear_combination hX)
    exact MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.some_eq_some (C • W) hx
      (mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination hY - (C.u : F) ^ 2 * C.s * hx))

variable [DecidableEq F]

/-- Transport of the affine point group along an equality of Weierstrass curves. -/
def equivOfEq {V V' : WeierstrassCurve F} (h : V = V') :
    V.toAffine.Point ≃+ V'.toAffine.Point := by
  subst h
  exact AddEquiv.refl _

@[simp] lemma equivOfEq_some {V V' : WeierstrassCurve F} (h : V = V') {x y : F}
    (hns : V.toAffine.Nonsingular x y) :
    MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.equivOfEq h (some x y hns) = some x y (h ▸ hns) := by
  subst h
  rfl

/-- The group homomorphism induced by the admissible change of variables. -/
def mapVariableChange : (C • W).toAffine.Point →+ W.toAffine.Point where
  toFun := MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.mapVariableChangeFun W C
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    simp only [MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.mapVariableChangeFun_some]
    have e₁ : (C • W).toAffine.Equation x₁ y₁ := h₁.left
    have e₂ : (C • W).toAffine.Equation x₂ y₂ := h₂.left
    by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
    · rw [add_of_Y_eq hxy.1 hxy.2, MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.mapVariableChangeFun_zero]
      refine (add_of_Y_eq ?_ ?_).symm
      · rw [hxy.1]
      · rw [MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.variableChange_negY, hxy.2, hxy.1]
    · rw [add_some hxy, MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.mapVariableChangeFun_some, add_some (MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.variableChange_negY_ne W C hxy)]
      simp only [MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.variableChange_slope W C e₁ e₂ hxy, MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.variableChange_addX, MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.variableChange_addY]

/-- The point-group isomorphism induced by the admissible change of variables. -/
def equivVariableChange : (C • W).toAffine.Point ≃+ W.toAffine.Point :=
  have hright : ∀ P, MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.mapVariableChangeFun W C
      (MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.mapVariableChangeFun (C • W) C⁻¹ (MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.equivOfEq (inv_smul_smul C W).symm P)) = P := by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    rintro (_ | ⟨X, Y, h⟩)
    · simp [← zero_def]
    · rw [MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.equivOfEq_some, MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.mapVariableChangeFun_some, MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.mapVariableChangeFun_some]
      refine MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.some_eq_some W ?_ ?_ <;>
        (simp only [VariableChange.inv_def, Units.val_inv_eq_inv_val]; field)
  { toFun := MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.mapVariableChangeFun W C
    invFun := fun P ↦ MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.mapVariableChangeFun (C • W) C⁻¹ (MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.equivOfEq (inv_smul_smul C W).symm P)
    left_inv := Function.RightInverse.leftInverse_of_injective hright
      (MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.mapVariableChangeFun_injective W C)
    right_inv := hright
    map_add' := (MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.mapVariableChange W C).map_add' }

lemma equivVariableChange_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.equivVariableChange W C (.some x y h)
      = .some ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
          ((MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.variableChange_nonsingular W C x y).mpr h) := rfl

end Point

end WeierstrassCurve.Affine

end

end MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair

namespace MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair
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
    refine MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.some_eq_some W ?_ ?_
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
  exact MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.some_eq_some W hx hy

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
  obtain ⟨h₂, hdouble⟩ := MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.two_mul_origin_coordinates b c hb h00
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
  exact MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.some_eq_some W hx hy

/-- In scalar-multiplication notation, `2P = (b,bc)` for the marked Tate point. -/
theorem two_nsmul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₂ : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular b (b * c),
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some b (b * c) h₂ := by
  simpa [two_nsmul] using MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.two_mul_origin_coordinates b c hb h00

/-- In scalar-multiplication notation, `3P = (c,b-c)` for the marked Tate point. -/
theorem three_nsmul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₃ : (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Nonsingular c (b - c),
      (3 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some c (b - c) h₃ := by
  obtain ⟨h₃, htriple⟩ := MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.three_mul_origin_coordinates b c hb h00
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
  obtain ⟨h₃, htriple⟩ := MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.three_mul_origin_coordinates b c hb h00
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
  exact MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.some_eq_some W hx hy


end MazurTorsion.Kubert

namespace MazurTorsion.ExceptionalTwoTen



end MazurTorsion.ExceptionalTwoTen

end
end MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair

namespace MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair
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
  obtain ⟨h₃, htriple⟩ := MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.three_nsmul_origin_coordinates b c hb h00
  have hc : c ≠ 0 := by
    intro hc0
    subst hc0
    have h3eq : (3 : ℕ) • P = -P := by
      rw [htriple, hPdef, WeierstrassCurve.Affine.Point.neg_some]
      exact MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.some_eq_some _ rfl
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
  obtain ⟨h₄, hquad⟩ := MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.four_mul_origin_coordinates b c hb hc h00
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
    exact (MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.three_nsmul_origin_coordinates b c hb h00).choose_spec
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
  rw [MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.orderSeven_Δ, MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.orderSeven_c₄]
  set K : ℚ := d ^ 3 - 8 * d ^ 2 + 5 * d + 1 with hKdef
  field_simp [hK]
  simp only [hKdef]
  ring

end MazurTorsion.Kubert

end
end MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair

namespace MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair
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
      MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.equivVariableChange W C₁
          (WeierstrassCurve.Affine.Point.some 0 0 h00₁) = P := by
    rw [MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.equivVariableChange_some]
    dsimp only [P]
    exact MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.some_eq_some W
      (by simp [C₁]) (by simp [C₁])
  have halpha : MazurTorsion.Kubert.pointTateAlpha W X Y ≠ 0 := by
    rw [← hC₁a₂]
    intro hzero
    apply hP3
    have htriple :
        WeierstrassCurve.Affine.Point.some 0 0 h00₁ +
            WeierstrassCurve.Affine.Point.some 0 0 h00₁ +
            WeierstrassCurve.Affine.Point.some 0 0 h00₁ = 0 :=
      MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.three_nsmul_origin_eq_zero (C₁ • W) hzero hC₁a₄
        (by rw [hC₁a₃]; exact hbeta) h00₁
    have himage :=
      congrArg (MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.equivVariableChange W C₁)
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
    (MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm.trans
      ((MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.equivVariableChange (C₁ • W) C₂).symm.trans
        (MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.equivOfEq hcurve))
  have heP : e P = WeierstrassCurve.Affine.Point.some 0 0 h00 := by
    have hfirst :
        (MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm P =
          WeierstrassCurve.Affine.Point.some 0 0 h00₁ := by
      rw [← hmap₁]
      exact (MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm_apply_apply _
    have hsecond :
        MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.equivVariableChange (C₁ • W) C₂
            (WeierstrassCurve.Affine.Point.some 0 0 h00₂) =
          WeierstrassCurve.Affine.Point.some 0 0 h00₁ := by
      rw [MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.equivVariableChange_some]
      exact MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.some_eq_some _
        (by simp [C₂]) (by simp [C₂])
    simp only [e, AddEquiv.trans_apply, hfirst, ← hsecond,
      AddEquiv.symm_apply_apply, MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.WeierstrassCurve.Affine.Point.equivOfEq_some]
  have h7P : (7 : ℕ) • P = 0 := by
    rw [← horder]
    exact addOrderOf_nsmul_eq_zero P
  have h7origin :
      (7 : ℕ) • (WeierstrassCurve.Affine.Point.some 0 0 h00 :
        (MazurTorsion.Kubert.tateNormalCurve b c).toAffine.Point) = 0 := by
    rw [← heP, ← map_nsmul, h7P, map_zero]
  obtain ⟨hc0, hrel⟩ := MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.orderSeven_tate_relation b c hb0 h00
    (WeierstrassCurve.Affine.Point.some_ne_zero h00) h7origin
  obtain ⟨d, hd0, hd1, hbeq, hceq⟩ :=
    MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.orderSeven_parametrization b c hb0 hc0 hrel
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
      rw [hbeq, hceq, MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.orderSeven_Δ, hK0]
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
  have hfam := MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.orderSeven_hauptmodul_identity d hd0 hd1 hK
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
end MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair

namespace MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/




open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert


















































































private theorem orderSevenB_ne_zero
    (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    MazurTorsion.Kubert.orderSevenB d ≠ 0 := by
  obtain ⟨hd0, hd1, -⟩ := MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.orderSevenFamily_parameters_ne d
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
  have hb : MazurTorsion.Kubert.orderSevenB d ≠ 0 := MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.orderSevenB_ne_zero d
  have h00 := MazurTorsion.Kubert.orderSevenOrigin_nonsingular d
  obtain ⟨h₂, htwo⟩ :=
    MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.two_nsmul_origin_coordinates (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) hb h00
  obtain ⟨h₃, hthree⟩ :=
    MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.three_nsmul_origin_coordinates (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) hb h00
  have hseven : (7 : ℕ) • P = 0 := MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.seven_nsmul_orderSevenOrigin d
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
    have hkilled := MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.seven_nsmul_of_kernelX hP hx
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
    MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.addOrderOf_orderSevenPointMap_of_order_fortyNine hQ hkernel hmap
  have horderVelu :
      addOrderOf (MazurTorsion.Kubert.orderSevenVeluPoint hP hx0 hxb hxc) = 7 := by
    rw [← MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.orderSevenPointMap_some_of_not_kernelX hP hx]
    exact horderImage
  have hspec := MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.orderSevenHauptmodulAt_spec
    (MazurTorsion.Kubert.orderSevenQuotient d)
    ((MazurTorsion.Kubert.orderSevenQuotient d).toAffine.equation_iff_nonsingular.mp
      (MazurTorsion.Kubert.orderSevenVelu_equation hP.1 hx0 hxb hxc))
    (by simpa only [MazurTorsion.Kubert.orderSevenVeluPoint] using horderVelu)
  simpa only [MazurTorsion.Kubert.orderSevenResidualHauptmodul] using hspec





end MazurTorsion.Kubert

end MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair

namespace MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert































































/-- The explicit residual Hauptmodul satisfies its quotient identity from
the zero-fiber hypothesis alone. -/
theorem orderSevenResidualHauptmodul_spec_of_order_fortyNine_of_kernel
    {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
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
  exact MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.orderSevenResidualHauptmodul_spec_of_order_fortyNine
    hP hQ hkernel
      (MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.orderSevenPointMap_seven_nsmul_of_order_fortyNine hQ hkernel)



end MazurTorsion.Kubert

end MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair

theorem solution {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
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
  apply MazurTransfer.Order49ResidualHauptmodulSpecConsumerRootMapZeroScopeRepair.MazurTorsion.Kubert.orderSevenResidualHauptmodul_spec_of_order_fortyNine_of_kernel <;> assumption
#print axioms solution
