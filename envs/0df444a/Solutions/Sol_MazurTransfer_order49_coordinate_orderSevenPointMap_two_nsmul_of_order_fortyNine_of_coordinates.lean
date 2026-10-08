-- Prove2me | solution 1 for MazurTransfer.order49_coordinate_orderSevenPointMap_two_nsmul_of_order_fortyNine_of_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T04:13:31.770775+00:00
-- url     : https://prove2.me/submissions/ab712bfe-bd4a-489f-ba45-ecc62f26f7d1

import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49DoublingCoordinateFormulas
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
import Mathlib
import Theorems.Thm_MazurTransfer_order49_doubling_geometry_orderSeven_kernel_double_certificate
import Theorems.Thm_MazurTransfer_order49_geometry_orderSevenVeluDifferential_eq_div
import Theorems.Thm_MazurTransfer_order49_geometry_orderSevenVelu_completedY
import Theorems.Thm_MazurTransfer_order49_point_map_not_orderSevenKernelX_of_order_fortyNine
import Theorems.Thm_MazurTransfer_order49_point_map_orderSevenPointMap_some_of_not_kernelX
import Theorems.Thm_MazurTransfer_order49_point_map_two_nsmul_ne_zero_of_order_fortyNine
open Polynomial
open _root_.WeierstrassCurve
open _root_.WeierstrassCurve.Affine
open _root_.WeierstrassCurve.Affine.Point hiding neg_zero
theorem MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.not_orderSevenKernelX_of_order_fortyNine {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (horder : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49) :
    ¬MazurTorsion.Kubert.OrderSevenKernelX d x := by
  apply MazurTransfer.order49_point_map_not_orderSevenKernelX_of_order_fortyNine <;> assumption

theorem MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenPointMap_some_of_not_kernelX {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hx : ¬MazurTorsion.Kubert.OrderSevenKernelX d x) :
    MazurTorsion.Kubert.orderSevenPointMap d (.some x y hP) =
      MazurTorsion.Kubert.orderSevenVeluPoint hP
        (fun h ↦ hx (Or.inl h))
        (fun h ↦ hx (Or.inr (Or.inl h)))
        (fun h ↦ hx (Or.inr (Or.inr h))) := by
  apply MazurTransfer.order49_point_map_orderSevenPointMap_some_of_not_kernelX <;> assumption

theorem MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenVeluDifferential_eq_div {d x : ℚ} (hx0 : x ≠ 0)
    (hxb : x ≠ MazurTorsion.Kubert.orderSevenB d)
    (hxc : x ≠ MazurTorsion.Kubert.orderSevenC d) :
    MazurTorsion.Kubert.orderSevenVeluDifferential d x =
      MazurTorsion.Kubert.orderSevenVeluDifferentialNumerator d x /
        MazurTorsion.Kubert.orderSevenKernelPolynomial d x ^ 3 := by
  apply MazurTransfer.order49_geometry_orderSevenVeluDifferential_eq_div <;> assumption

theorem MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenVelu_completedY (d x y : ℚ) :
    2 * MazurTorsion.Kubert.orderSevenVeluY d x y +
        (MazurTorsion.Kubert.orderSevenQuotient d).a₁ * MazurTorsion.Kubert.orderSevenVeluX d x +
        (MazurTorsion.Kubert.orderSevenQuotient d).a₃ =
      MazurTorsion.Kubert.orderSevenVeluDifferential d x *
        (2 * y + (MazurTorsion.Kubert.orderSevenFamily d).a₁ * x +
          (MazurTorsion.Kubert.orderSevenFamily d).a₃) := by
  apply MazurTransfer.order49_geometry_orderSevenVelu_completedY <;> assumption

theorem MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSeven_kernel_double_certificate (d x : ℚ) :
    let H := MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x
    let p := MazurTorsion.Doubling.xNumerator (MazurTorsion.Kubert.orderSevenFamily d) x
    p * (p - MazurTorsion.Kubert.orderSevenB d * H) * (p - MazurTorsion.Kubert.orderSevenC d * H) =
      MazurTorsion.Kubert.orderSevenKernelPolynomial d x *
        MazurTorsion.Kubert.orderSevenVeluDifferentialNumerator d x := by
  apply MazurTransfer.order49_doubling_geometry_orderSeven_kernel_double_certificate <;> assumption

theorem MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.two_nsmul_ne_zero_of_order_fortyNine {G : Type*} [AddCommGroup G] {P : G}
    (hP : addOrderOf P = 49) :
    (2 : ℕ) • P ≠ 0 := by
  apply MazurTransfer.order49_point_map_two_nsmul_ne_zero_of_order_fortyNine <;> assumption
namespace MazurTransfer.Order49DoublingCoordinateConsumers
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

/-- The tangent-law doubling abscissa times the completed-square cubic is
the denominator-free numerator `xNumerator`. -/
theorem addX_self_mul_completedCubic
    (W : WeierstrassCurve ℚ) {x y : ℚ}
    (h : W.toAffine.Equation x y)
    (hv : 2 * y + W.a₁ * x + W.a₃ ≠ 0) :
    W.toAffine.addX x x (W.toAffine.slope x x y y) *
        MazurTorsion.Doubling.completedCubic W x = MazurTorsion.Doubling.xNumerator W x := by
  let v : ℚ := 2 * y + W.a₁ * x + W.a₃
  let n : ℚ := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y
  let m : ℚ := W.toAffine.slope x x y y
  have hy : y ≠ W.toAffine.negY x y := by
    intro hy
    apply hv
    simp only [WeierstrassCurve.Affine.negY] at hy
    linarith
  have hm : m * v = n := by
    dsimp only [m]
    rw [W.toAffine.slope_of_Y_ne rfl hy]
    convert
      (div_mul_cancel₀
        (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) hv)
        using 1
    all_goals
      simp only [v, WeierstrassCurve.Affine.negY,
        WeierstrassCurve.toAffine]
      ring
  have hc := h
  rw [WeierstrassCurve.Affine.equation_iff] at hc
  change y ^ 2 + W.a₁ * x * y + W.a₃ * y =
    x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ at hc
  rw [MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Doubling.completedCubic_eq_completedY_sq W h]
  rw [WeierstrassCurve.Affine.addX]
  simp only [WeierstrassCurve.toAffine]
  change (m ^ 2 + W.a₁ * m - W.a₂ - x - x) * v ^ 2 =
    MazurTorsion.Doubling.xNumerator W x
  simp only [MazurTorsion.Doubling.xNumerator, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  linear_combination
    (m * v + n + W.a₁ * v) * hm -
      (W.a₁ ^ 2 + 4 * W.a₂ + 8 * x) * hc



end MazurTorsion.Doubling

end
end MazurTransfer.Order49DoublingCoordinateConsumers

namespace MazurTransfer.Order49DoublingCoordinateConsumers
/-
Copyright (c) 2026 Kevin Buzzard, Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude, Vasily Ilin
-/




section

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (C : VariableChange F)

























namespace Point







lemma some_eq_some (W : WeierstrassCurve F) {x₁ x₂ y₁ y₂ : F} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : W.toAffine.Nonsingular x₁ y₁} {h₂ : W.toAffine.Nonsingular x₂ y₂} :
    (some x₁ y₁ h₁ : W.toAffine.Point) = some x₂ y₂ h₂ := by
  subst hx hy
  rfl



variable [DecidableEq F]











end Point

end WeierstrassCurve.Affine

end

end MazurTransfer.Order49DoublingCoordinateConsumers

namespace MazurTransfer.Order49DoublingCoordinateConsumers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

































private theorem kernelPolynomial_at_double
    {b c H p x₂ K N : ℚ}
    (hp : p = x₂ * H)
    (hcert : p * (p - b * H) * (p - c * H) = K * N) :
    x₂ * (x₂ - b) * (x₂ - c) * H ^ 3 = K * N := by
  rw [hp] at hcert
  linear_combination hcert













private theorem orderSevenVeluPoint_two_nsmul_of_coordinates
    {d x y x₂ y₂ : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hP₂ : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x₂ y₂)
    (hx0 : x ≠ 0) (hxb : x ≠ MazurTorsion.Kubert.orderSevenB d)
    (hxc : x ≠ MazurTorsion.Kubert.orderSevenC d)
    (hx0₂ : x₂ ≠ 0) (hxb₂ : x₂ ≠ MazurTorsion.Kubert.orderSevenB d)
    (hxc₂ : x₂ ≠ MazurTorsion.Kubert.orderSevenC d)
    (hcompletedY :
      2 * MazurTorsion.Kubert.orderSevenVeluY d x y +
          (MazurTorsion.Kubert.orderSevenQuotient d).toAffine.a₁ * MazurTorsion.Kubert.orderSevenVeluX d x +
          (MazurTorsion.Kubert.orderSevenQuotient d).toAffine.a₃ ≠ 0)
    (hX : MazurTorsion.Kubert.orderSevenVeluX d x₂ =
      (MazurTorsion.Kubert.orderSevenQuotient d).toAffine.addX
        (MazurTorsion.Kubert.orderSevenVeluX d x) (MazurTorsion.Kubert.orderSevenVeluX d x)
        ((MazurTorsion.Kubert.orderSevenQuotient d).toAffine.slope
          (MazurTorsion.Kubert.orderSevenVeluX d x) (MazurTorsion.Kubert.orderSevenVeluX d x)
          (MazurTorsion.Kubert.orderSevenVeluY d x y) (MazurTorsion.Kubert.orderSevenVeluY d x y)))
    (hcompleted :
      2 * MazurTorsion.Kubert.orderSevenVeluY d x₂ y₂ +
          (MazurTorsion.Kubert.orderSevenQuotient d).toAffine.a₁ * MazurTorsion.Kubert.orderSevenVeluX d x₂ +
          (MazurTorsion.Kubert.orderSevenQuotient d).toAffine.a₃ =
        2 * (MazurTorsion.Kubert.orderSevenQuotient d).toAffine.addY
            (MazurTorsion.Kubert.orderSevenVeluX d x) (MazurTorsion.Kubert.orderSevenVeluX d x)
            (MazurTorsion.Kubert.orderSevenVeluY d x y)
            ((MazurTorsion.Kubert.orderSevenQuotient d).toAffine.slope
              (MazurTorsion.Kubert.orderSevenVeluX d x) (MazurTorsion.Kubert.orderSevenVeluX d x)
              (MazurTorsion.Kubert.orderSevenVeluY d x y) (MazurTorsion.Kubert.orderSevenVeluY d x y)) +
          (MazurTorsion.Kubert.orderSevenQuotient d).toAffine.a₁ *
            (MazurTorsion.Kubert.orderSevenQuotient d).toAffine.addX
              (MazurTorsion.Kubert.orderSevenVeluX d x) (MazurTorsion.Kubert.orderSevenVeluX d x)
              ((MazurTorsion.Kubert.orderSevenQuotient d).toAffine.slope
                (MazurTorsion.Kubert.orderSevenVeluX d x) (MazurTorsion.Kubert.orderSevenVeluX d x)
                (MazurTorsion.Kubert.orderSevenVeluY d x y) (MazurTorsion.Kubert.orderSevenVeluY d x y)) +
          (MazurTorsion.Kubert.orderSevenQuotient d).toAffine.a₃) :
    MazurTorsion.Kubert.orderSevenVeluPoint hP₂ hx0₂ hxb₂ hxc₂ =
      (2 : ℕ) • MazurTorsion.Kubert.orderSevenVeluPoint hP hx0 hxb hxc := by
  have hYne : MazurTorsion.Kubert.orderSevenVeluY d x y ≠
      (MazurTorsion.Kubert.orderSevenQuotient d).toAffine.negY
        (MazurTorsion.Kubert.orderSevenVeluX d x) (MazurTorsion.Kubert.orderSevenVeluY d x y) := by
    intro hY
    apply hcompletedY
    simp only [WeierstrassCurve.Affine.negY] at hY
    linear_combination hY
  rw [two_nsmul]
  simp only [MazurTorsion.Kubert.orderSevenVeluPoint]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hYne]
  apply MazurTransfer.Order49DoublingCoordinateConsumers.WeierstrassCurve.Affine.Point.some_eq_some
    (MazurTorsion.Kubert.orderSevenQuotient d)
  · exact hX
  · linear_combination
      (1 / 2 : ℚ) * hcompleted -
        ((MazurTorsion.Kubert.orderSevenQuotient d).toAffine.a₁ / 2) * hX

private theorem orderSevenPointMap_two_nsmul_of_order_fortyNine_affine
    {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (horder : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49)
    (hcoordinates : MazurTorsion.Kubert.OrderSevenDoublingCoordinates d x y) :
    MazurTorsion.Kubert.orderSevenPointMap d
        ((2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y hP :
          (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point)) =
      (2 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d
        (WeierstrassCurve.Affine.Point.some x y hP) := by
  let W := (MazurTorsion.Kubert.orderSevenFamily d).toAffine
  let m := W.slope x x y y
  let x₂ := W.addX x x m
  let y₂ := W.addY x x y m
  have htwo_ne :
      (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) ≠ 0 :=
    MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.two_nsmul_ne_zero_of_order_fortyNine horder
  have hy : y ≠ W.negY x y := by
    intro hy
    apply htwo_ne
    rw [two_nsmul]
    exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy
  let hP₂ : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x₂ y₂ :=
    W.nonsingular_add hP hP (fun hxy ↦ hy hxy.2)
  have hadd :
      (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y hP :
          (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) =
        WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ := by
    rw [two_nsmul,
      WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
  have horder₂ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49 := by
    rw [← hadd, addOrderOf_nsmul'
      (WeierstrassCurve.Affine.Point.some x y hP) (by norm_num), horder]
    norm_num
  have hx := MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.not_orderSevenKernelX_of_order_fortyNine hP horder
  have hx₂ := MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.not_orderSevenKernelX_of_order_fortyNine hP₂ horder₂
  have hx0 : x ≠ 0 := fun h ↦ hx (Or.inl h)
  have hxb : x ≠ MazurTorsion.Kubert.orderSevenB d :=
    fun h ↦ hx (Or.inr (Or.inl h))
  have hxc : x ≠ MazurTorsion.Kubert.orderSevenC d :=
    fun h ↦ hx (Or.inr (Or.inr h))
  have hx0₂ : x₂ ≠ 0 := fun h ↦ hx₂ (Or.inl h)
  have hxb₂ : x₂ ≠ MazurTorsion.Kubert.orderSevenB d :=
    fun h ↦ hx₂ (Or.inr (Or.inl h))
  have hxc₂ : x₂ ≠ MazurTorsion.Kubert.orderSevenC d :=
    fun h ↦ hx₂ (Or.inr (Or.inr h))
  have hK : MazurTorsion.Kubert.orderSevenKernelPolynomial d x ≠ 0 :=
    mul_ne_zero (mul_ne_zero hx0 (sub_ne_zero.mpr hxb))
      (sub_ne_zero.mpr hxc)
  have hK₂ : MazurTorsion.Kubert.orderSevenKernelPolynomial d x₂ ≠ 0 :=
    mul_ne_zero (mul_ne_zero hx0₂ (sub_ne_zero.mpr hxb₂))
      (sub_ne_zero.mpr hxc₂)
  have hv : 2 * y + (MazurTorsion.Kubert.orderSevenFamily d).a₁ * x +
      (MazurTorsion.Kubert.orderSevenFamily d).a₃ ≠ 0 := by
    intro hv
    apply hy
    simp only [W, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.toAffine]
    linarith
  have hH : MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x ≠ 0 := by
    rw [MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Doubling.completedCubic_eq_completedY_sq
      (MazurTorsion.Kubert.orderSevenFamily d) hP.1]
    exact pow_ne_zero 2 hv
  have hp : MazurTorsion.Doubling.xNumerator (MazurTorsion.Kubert.orderSevenFamily d) x =
      x₂ * MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x :=
    (MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Doubling.addX_self_mul_completedCubic
      (MazurTorsion.Kubert.orderSevenFamily d) hP.1 hv).symm
  have hkernel :
      MazurTorsion.Kubert.orderSevenKernelPolynomial d x₂ *
          MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x ^ 3 =
        MazurTorsion.Kubert.orderSevenKernelPolynomial d x *
          MazurTorsion.Kubert.orderSevenVeluDifferentialNumerator d x := by
    exact MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.kernelPolynomial_at_double hp
      (MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSeven_kernel_double_certificate d x)
  have hN : MazurTorsion.Kubert.orderSevenVeluDifferentialNumerator d x ≠ 0 := by
    intro hN
    have hleft : MazurTorsion.Kubert.orderSevenKernelPolynomial d x₂ *
        MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x ^ 3 ≠ 0 :=
      mul_ne_zero hK₂ (pow_ne_zero 3 hH)
    apply hleft
    rw [hkernel, hN, mul_zero]
  have hdiff : MazurTorsion.Kubert.orderSevenVeluDifferential d x ≠ 0 := by
    rw [MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenVeluDifferential_eq_div hx0 hxb hxc]
    exact div_ne_zero hN (pow_ne_zero 3 hK)
  have hcompletedY :
      2 * MazurTorsion.Kubert.orderSevenVeluY d x y +
          (MazurTorsion.Kubert.orderSevenQuotient d).toAffine.a₁ * MazurTorsion.Kubert.orderSevenVeluX d x +
          (MazurTorsion.Kubert.orderSevenQuotient d).toAffine.a₃ ≠ 0 := by
    rw [MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenVelu_completedY]
    exact mul_ne_zero hdiff hv
  obtain ⟨hX, hcompleted⟩ := hcoordinates
  rw [hadd, MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenPointMap_some_of_not_kernelX hP₂ hx₂,
    MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenPointMap_some_of_not_kernelX hP hx]
  exact MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenVeluPoint_two_nsmul_of_coordinates hP hP₂
    hx0 hxb hxc hx0₂ hxb₂ hxc₂ hcompletedY hX hcompleted

private theorem orderSevenPointMap_two_nsmul_of_order_fortyNine_of_coordinates
    {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hcoordinates : ∀ {x y : ℚ}
      (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y),
      addOrderOf
          (WeierstrassCurve.Affine.Point.some x y hP :
            (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49 →
        MazurTorsion.Kubert.OrderSevenDoublingCoordinates d x y)
    {Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49) :
    MazurTorsion.Kubert.orderSevenPointMap d ((2 : ℕ) • Q) =
      (2 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d Q := by
  cases Q with
  | zero =>
      have hfalse : (1 : ℕ) = 49 := by
        rw [← hQ]
        exact (addOrderOf_zero
          (G := (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point)).symm
      norm_num at hfalse
  | some x y hP =>
      exact MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenPointMap_two_nsmul_of_order_fortyNine_affine
        hP hQ (hcoordinates hP hQ)















end MazurTorsion.Kubert

end MazurTransfer.Order49DoublingCoordinateConsumers

theorem solution {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hcoordinates : ∀ {x y : ℚ}
      (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y),
      addOrderOf
          (WeierstrassCurve.Affine.Point.some x y hP :
            (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49 →
        MazurTorsion.Kubert.OrderSevenDoublingCoordinates d x y)
    {Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49) :
    MazurTorsion.Kubert.orderSevenPointMap d ((2 : ℕ) • Q) =
      (2 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d Q := by
  apply MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenPointMap_two_nsmul_of_order_fortyNine_of_coordinates <;> assumption
#print axioms solution
