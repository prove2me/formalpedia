-- Prove2me | solution 1 for MazurTransfer.order49_coordinate_orderSevenVelu_double_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T04:14:42.005752+00:00
-- url     : https://prove2.me/submissions/eb218723-6798-4c20-888a-7906625707f3

import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49DoublingCoordinateFormulas
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
import Mathlib
import Theorems.Thm_MazurTransfer_order49_doubling_geometry_orderSevenVeluDifferential_double_homogeneous
import Theorems.Thm_MazurTransfer_order49_doubling_geometry_orderSevenVeluX_double_homogeneous
import Theorems.Thm_MazurTransfer_order49_doubling_geometry_orderSeven_kernel_double_certificate
import Theorems.Thm_MazurTransfer_order49_geometry_orderSevenVeluDifferential_eq_div
import Theorems.Thm_MazurTransfer_order49_geometry_orderSevenVeluX_eq_div
import Theorems.Thm_MazurTransfer_order49_geometry_orderSevenVelu_completedSquare
import Theorems.Thm_MazurTransfer_order49_geometry_orderSevenVelu_completedY
import Theorems.Thm_MazurTransfer_order49_point_map_not_orderSevenKernelX_of_order_fortyNine
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

theorem MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenVeluDifferential_eq_div {d x : ℚ} (hx0 : x ≠ 0)
    (hxb : x ≠ MazurTorsion.Kubert.orderSevenB d)
    (hxc : x ≠ MazurTorsion.Kubert.orderSevenC d) :
    MazurTorsion.Kubert.orderSevenVeluDifferential d x =
      MazurTorsion.Kubert.orderSevenVeluDifferentialNumerator d x /
        MazurTorsion.Kubert.orderSevenKernelPolynomial d x ^ 3 := by
  apply MazurTransfer.order49_geometry_orderSevenVeluDifferential_eq_div <;> assumption

theorem MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenVeluX_eq_div {d x : ℚ} (hx0 : x ≠ 0)
    (hxb : x ≠ MazurTorsion.Kubert.orderSevenB d)
    (hxc : x ≠ MazurTorsion.Kubert.orderSevenC d) :
    MazurTorsion.Kubert.orderSevenVeluX d x =
      MazurTorsion.Kubert.orderSevenVeluXNumerator d x /
        MazurTorsion.Kubert.orderSevenKernelPolynomial d x ^ 2 := by
  apply MazurTransfer.order49_geometry_orderSevenVeluX_eq_div <;> assumption

theorem MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenVelu_completedSquare {d x : ℚ} (hx0 : x ≠ 0)
    (hxb : x ≠ MazurTorsion.Kubert.orderSevenB d)
    (hxc : x ≠ MazurTorsion.Kubert.orderSevenC d) :
    MazurTorsion.Kubert.orderSevenVeluDifferential d x ^ 2 *
        (4 * x ^ 3 + (MazurTorsion.Kubert.orderSevenFamily d).b₂ * x ^ 2 +
          2 * (MazurTorsion.Kubert.orderSevenFamily d).b₄ * x +
          (MazurTorsion.Kubert.orderSevenFamily d).b₆) =
      4 * MazurTorsion.Kubert.orderSevenVeluX d x ^ 3 +
        (MazurTorsion.Kubert.orderSevenQuotient d).b₂ * MazurTorsion.Kubert.orderSevenVeluX d x ^ 2 +
        2 * (MazurTorsion.Kubert.orderSevenQuotient d).b₄ * MazurTorsion.Kubert.orderSevenVeluX d x +
        (MazurTorsion.Kubert.orderSevenQuotient d).b₆ := by
  apply MazurTransfer.order49_geometry_orderSevenVelu_completedSquare <;> assumption

theorem MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenVelu_completedY (d x y : ℚ) :
    2 * MazurTorsion.Kubert.orderSevenVeluY d x y +
        (MazurTorsion.Kubert.orderSevenQuotient d).a₁ * MazurTorsion.Kubert.orderSevenVeluX d x +
        (MazurTorsion.Kubert.orderSevenQuotient d).a₃ =
      MazurTorsion.Kubert.orderSevenVeluDifferential d x *
        (2 * y + (MazurTorsion.Kubert.orderSevenFamily d).a₁ * x +
          (MazurTorsion.Kubert.orderSevenFamily d).a₃) := by
  apply MazurTransfer.order49_geometry_orderSevenVelu_completedY <;> assumption

theorem MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenVeluDifferential_double_homogeneous (d x : ℚ)
    (hK : MazurTorsion.Kubert.orderSevenKernelPolynomial d x ≠ 0)
    (hN : MazurTorsion.Kubert.orderSevenVeluDifferentialNumerator d x ≠ 0) :
    MazurTorsion.Kubert.orderSevenVeluDifferentialNumeratorHomogeneous d
        (MazurTorsion.Doubling.xNumerator (MazurTorsion.Kubert.orderSevenFamily d) x)
        (MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x) *
          MazurTorsion.Doubling.completedYNumerator (MazurTorsion.Kubert.orderSevenFamily d) x =
      MazurTorsion.Doubling.completedYNumeratorHomogeneous (MazurTorsion.Kubert.orderSevenQuotient d)
        (MazurTorsion.Kubert.orderSevenVeluXNumerator d x)
        (MazurTorsion.Kubert.orderSevenKernelPolynomial d x ^ 2) := by
  apply MazurTransfer.order49_doubling_geometry_orderSevenVeluDifferential_double_homogeneous <;> assumption

theorem MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenVeluX_double_homogeneous (d x : ℚ) :
    MazurTorsion.Kubert.orderSevenVeluXNumeratorHomogeneous d
        (MazurTorsion.Doubling.xNumerator (MazurTorsion.Kubert.orderSevenFamily d) x)
        (MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x) =
      MazurTorsion.Doubling.xNumeratorHomogeneous (MazurTorsion.Kubert.orderSevenQuotient d)
        (MazurTorsion.Kubert.orderSevenVeluXNumerator d x)
        (MazurTorsion.Kubert.orderSevenKernelPolynomial d x ^ 2) := by
  apply MazurTransfer.order49_doubling_geometry_orderSevenVeluX_double_homogeneous <;> assumption

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

/-- The completed ordinate of an affine double, multiplied by the cube of
the source completed ordinate, is `completedYNumerator`. -/
theorem completedY_add_self
    (W : WeierstrassCurve ℚ) {x y : ℚ}
    (h : W.toAffine.Equation x y)
    (hv : 2 * y + W.a₁ * x + W.a₃ ≠ 0) :
    (2 * y + W.a₁ * x + W.a₃) ^ 3 *
      (2 * W.toAffine.addY x x y (W.toAffine.slope x x y y) +
        W.a₁ * W.toAffine.addX x x (W.toAffine.slope x x y y) +
        W.a₃) =
      MazurTorsion.Doubling.completedYNumerator W x := by
  let v : ℚ := 2 * y + W.a₁ * x + W.a₃
  let n : ℚ := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y
  let m : ℚ := W.toAffine.slope x x y y
  let q : ℚ := W.toAffine.addX x x m
  let r : ℚ := W.toAffine.addY x x y m
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
  have hq : q * v ^ 2 = MazurTorsion.Doubling.xNumerator W x := by
    have ht := MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Doubling.addX_self_mul_completedCubic W h hv
    rw [MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Doubling.completedCubic_eq_completedY_sq W h] at ht
    simpa only [q, m, v] using ht
  have hr : 2 * r + W.a₁ * q + W.a₃ =
      -(2 * m + W.a₁) * (q - x) - v := by
    simp only [r, q, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY]
    ring
  change v ^ 3 * (2 * r + W.a₁ * q + W.a₃) =
    MazurTorsion.Doubling.completedYNumerator W x
  simp only [MazurTorsion.Doubling.completedYNumerator, MazurTorsion.Doubling.xNumerator,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈] at hq ⊢
  linear_combination
    v ^ 3 * hr - 2 * v ^ 2 * (q - x) * hm -
      (2 * n + W.a₁ * v) * hq +
      4 *
        (-W.a₁ ^ 2 * x ^ 2 - 3 * W.a₁ * W.a₃ * x -
          4 * W.a₁ * x * y - 2 * W.a₃ ^ 2 - 4 * W.a₃ * y -
          2 * W.a₄ * x - 4 * W.a₆ + 2 * x ^ 3 - 4 * y ^ 2) * hc

end MazurTorsion.Doubling

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













@[simp] theorem orderSevenVeluXNumeratorHomogeneous_at_one
    (d x : ℚ) :
    MazurTorsion.Kubert.orderSevenVeluXNumeratorHomogeneous d x 1 =
      MazurTorsion.Kubert.orderSevenVeluXNumerator d x := by
  simp only [MazurTorsion.Kubert.orderSevenVeluXNumeratorHomogeneous,
    MazurTorsion.Kubert.orderSevenVeluXNumerator]
  ring

@[simp] theorem orderSevenVeluDifferentialNumeratorHomogeneous_at_one
    (d x : ℚ) :
    MazurTorsion.Kubert.orderSevenVeluDifferentialNumeratorHomogeneous d x 1 =
      MazurTorsion.Kubert.orderSevenVeluDifferentialNumerator d x := by
  simp only [MazurTorsion.Kubert.orderSevenVeluDifferentialNumeratorHomogeneous,
    MazurTorsion.Kubert.orderSevenVeluDifferentialNumerator]
  ring









private theorem orderSevenVeluX_double_homogeneous_of_abscissa
    (d x x₂ : ℚ)
    (hx₂ : MazurTorsion.Doubling.xNumerator (MazurTorsion.Kubert.orderSevenFamily d) x =
      x₂ * MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x) :
    MazurTorsion.Kubert.orderSevenVeluXNumerator d x₂ *
        MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x ^ 7 =
      MazurTorsion.Doubling.xNumeratorHomogeneous (MazurTorsion.Kubert.orderSevenQuotient d)
        (MazurTorsion.Kubert.orderSevenVeluXNumerator d x)
        (MazurTorsion.Kubert.orderSevenKernelPolynomial d x ^ 2) := by
  rw [← MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenVeluXNumeratorHomogeneous_at_one]
  calc
    MazurTorsion.Kubert.orderSevenVeluXNumeratorHomogeneous d x₂ 1 *
          MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x ^ 7 =
        MazurTorsion.Kubert.orderSevenVeluXNumeratorHomogeneous d
          (x₂ * MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x)
          (MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x) := by
      simp only [MazurTorsion.Kubert.orderSevenVeluXNumeratorHomogeneous]
      ring
    _ = MazurTorsion.Kubert.orderSevenVeluXNumeratorHomogeneous d
          (MazurTorsion.Doubling.xNumerator (MazurTorsion.Kubert.orderSevenFamily d) x)
          (MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x) := by
      rw [hx₂]
    _ = MazurTorsion.Doubling.xNumeratorHomogeneous (MazurTorsion.Kubert.orderSevenQuotient d)
          (MazurTorsion.Kubert.orderSevenVeluXNumerator d x)
          (MazurTorsion.Kubert.orderSevenKernelPolynomial d x ^ 2) :=
      MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenVeluX_double_homogeneous d x





private theorem orderSevenVeluDifferential_double_homogeneous_of_abscissa
    (d x x₂ : ℚ)
    (hx₂ : MazurTorsion.Doubling.xNumerator (MazurTorsion.Kubert.orderSevenFamily d) x =
      x₂ * MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x)
    (hK : MazurTorsion.Kubert.orderSevenKernelPolynomial d x ≠ 0)
    (hN : MazurTorsion.Kubert.orderSevenVeluDifferentialNumerator d x ≠ 0) :
    MazurTorsion.Kubert.orderSevenVeluDifferentialNumerator d x₂ *
          MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x ^ 9 *
        MazurTorsion.Doubling.completedYNumerator (MazurTorsion.Kubert.orderSevenFamily d) x =
      MazurTorsion.Doubling.completedYNumeratorHomogeneous (MazurTorsion.Kubert.orderSevenQuotient d)
        (MazurTorsion.Kubert.orderSevenVeluXNumerator d x)
        (MazurTorsion.Kubert.orderSevenKernelPolynomial d x ^ 2) := by
  rw [← MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenVeluDifferentialNumeratorHomogeneous_at_one]
  calc
    MazurTorsion.Kubert.orderSevenVeluDifferentialNumeratorHomogeneous d x₂ 1 *
          MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x ^ 9 *
        MazurTorsion.Doubling.completedYNumerator (MazurTorsion.Kubert.orderSevenFamily d) x =
      MazurTorsion.Kubert.orderSevenVeluDifferentialNumeratorHomogeneous d
          (x₂ * MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x)
          (MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x) *
        MazurTorsion.Doubling.completedYNumerator (MazurTorsion.Kubert.orderSevenFamily d) x := by
      simp only [MazurTorsion.Kubert.orderSevenVeluDifferentialNumeratorHomogeneous]
      ring
    _ = MazurTorsion.Kubert.orderSevenVeluDifferentialNumeratorHomogeneous d
          (MazurTorsion.Doubling.xNumerator (MazurTorsion.Kubert.orderSevenFamily d) x)
          (MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x) *
        MazurTorsion.Doubling.completedYNumerator (MazurTorsion.Kubert.orderSevenFamily d) x := by
      rw [hx₂]
    _ = MazurTorsion.Doubling.completedYNumeratorHomogeneous (MazurTorsion.Kubert.orderSevenQuotient d)
          (MazurTorsion.Kubert.orderSevenVeluXNumerator d x)
          (MazurTorsion.Kubert.orderSevenKernelPolynomial d x ^ 2) :=
      MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenVeluDifferential_double_homogeneous d x hK hN

private theorem kernelPolynomial_at_double
    {b c H p x₂ K N : ℚ}
    (hp : p = x₂ * H)
    (hcert : p * (p - b * H) * (p - c * H) = K * N) :
    x₂ * (x₂ - b) * (x₂ - c) * H ^ 3 = K * N := by
  rw [hp] at hcert
  linear_combination hcert

private theorem quotient_doubleX_of_homogeneous
    {H F₂ K₂ K N PhiT : ℚ}
    (hH : H ≠ 0) (hK : K ≠ 0) (hN : N ≠ 0) (hK₂ : K₂ ≠ 0)
    (hkernel : K₂ * H ^ 3 = K * N)
    (hhom : F₂ * H ^ 7 = PhiT) :
    F₂ / K₂ ^ 2 =
      (PhiT / K ^ 8) / ((N / K ^ 3) ^ 2 * H) := by
  field_simp [hH, hK, hN, hK₂]
  have hkernel₂ : K₂ ^ 2 * H ^ 6 = K ^ 2 * N ^ 2 := by
    calc
      K₂ ^ 2 * H ^ 6 = (K₂ * H ^ 3) ^ 2 := by ring
      _ = (K * N) ^ 2 := by rw [hkernel]
      _ = K ^ 2 * N ^ 2 := by ring
  calc
    F₂ * K ^ 2 * N ^ 2 * H = F₂ * (K ^ 2 * N ^ 2) * H := by ring
    _ = F₂ * (K₂ ^ 2 * H ^ 6) * H := by rw [← hkernel₂]
    _ = K₂ ^ 2 * (F₂ * H ^ 7) := by ring
    _ = K₂ ^ 2 * PhiT := by rw [hhom]

private theorem quotient_doubleCompletedY_of_homogeneous
    {V H R V₂ N₂ K₂ K N RT : ℚ}
    (hV : V ≠ 0) (hK : K ≠ 0) (hN : N ≠ 0) (hK₂ : K₂ ≠ 0)
    (hH : H = V ^ 2)
    (hsource : V ^ 3 * V₂ = R)
    (hkernel : K₂ * H ^ 3 = K * N)
    (hhom : N₂ * H ^ 9 * R = RT) :
    (N₂ / K₂ ^ 3) * V₂ =
      (RT / K ^ 12) / ((N / K ^ 3 * V) ^ 3) := by
  field_simp [hV, hK, hN, hK₂]
  rw [hH] at hkernel hhom
  have hkernel₃ : K₂ ^ 3 * V ^ 18 = K ^ 3 * N ^ 3 := by
    calc
      K₂ ^ 3 * V ^ 18 = (K₂ * (V ^ 2) ^ 3) ^ 3 := by ring
      _ = (K * N) ^ 3 := by rw [hkernel]
      _ = K ^ 3 * N ^ 3 := by ring
  calc
    N₂ * V₂ * K ^ 3 * N ^ 3 * V ^ 3 =
        N₂ * V₂ * (K ^ 3 * N ^ 3) * V ^ 3 := by ring
    _ = N₂ * V₂ * (K₂ ^ 3 * V ^ 18) * V ^ 3 := by
      rw [← hkernel₃]
    _ = K₂ ^ 3 * (N₂ * V ^ 18 * (V ^ 3 * V₂)) := by ring
    _ = K₂ ^ 3 * (N₂ * V ^ 18 * R) := by rw [hsource]
    _ = K₂ ^ 3 * RT := by
      rw [← hhom]
      ring

private theorem xNumerator_div_square
    (W : WeierstrassCurve ℚ) {u k : ℚ} (hk : k ≠ 0) :
    MazurTorsion.Doubling.xNumerator W (u / k ^ 2) =
      MazurTorsion.Doubling.xNumeratorHomogeneous W u (k ^ 2) / k ^ 8 := by
  simp only [MazurTorsion.Doubling.xNumerator, MazurTorsion.Doubling.xNumeratorHomogeneous]
  field_simp [hk]

private theorem completedYNumerator_div_square
    (W : WeierstrassCurve ℚ) {u k : ℚ} (hk : k ≠ 0) :
    MazurTorsion.Doubling.completedYNumerator W (u / k ^ 2) =
      MazurTorsion.Doubling.completedYNumeratorHomogeneous W u (k ^ 2) /
        k ^ 12 := by
  simp only [MazurTorsion.Doubling.completedYNumerator,
    MazurTorsion.Doubling.completedYNumeratorHomogeneous]
  field_simp [hk]











private theorem orderSevenVelu_double_coordinates
    {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (horder : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49) :
    MazurTorsion.Kubert.OrderSevenDoublingCoordinates d x y := by
  let W := MazurTorsion.Kubert.orderSevenFamily d
  let Wq := MazurTorsion.Kubert.orderSevenQuotient d
  let m := W.toAffine.slope x x y y
  let x₂ := W.toAffine.addX x x m
  let y₂ := W.toAffine.addY x x y m
  let X := MazurTorsion.Kubert.orderSevenVeluX d x
  let Y := MazurTorsion.Kubert.orderSevenVeluY d x y
  let M := Wq.toAffine.slope X X Y Y
  let X₂ := Wq.toAffine.addX X X M
  let Y₂ := Wq.toAffine.addY X X Y M
  change MazurTorsion.Kubert.orderSevenVeluX d x₂ = X₂ ∧
    2 * MazurTorsion.Kubert.orderSevenVeluY d x₂ y₂ + Wq.a₁ * MazurTorsion.Kubert.orderSevenVeluX d x₂ +
        Wq.a₃ = 2 * Y₂ + Wq.a₁ * X₂ + Wq.a₃
  have htwo_ne :
      (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) ≠ 0 :=
    MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.two_nsmul_ne_zero_of_order_fortyNine horder
  have hy : y ≠ W.toAffine.negY x y := by
    intro hy
    apply htwo_ne
    rw [two_nsmul]
    exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy
  let hP₂ : W.toAffine.Nonsingular x₂ y₂ :=
    W.toAffine.nonsingular_add hP hP (fun hxy ↦ hy hxy.2)
  have hadd :
      (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y hP :
          W.toAffine.Point) =
        WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ := by
    rw [two_nsmul,
      WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
  have horder₂ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ :
        W.toAffine.Point) = 49 := by
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
  let V := 2 * y + W.a₁ * x + W.a₃
  let V₂ := 2 * y₂ + W.a₁ * x₂ + W.a₃
  let H := MazurTorsion.Doubling.completedCubic W x
  let p := MazurTorsion.Doubling.xNumerator W x
  let K := MazurTorsion.Kubert.orderSevenKernelPolynomial d x
  let K₂ := MazurTorsion.Kubert.orderSevenKernelPolynomial d x₂
  let N := MazurTorsion.Kubert.orderSevenVeluDifferentialNumerator d x
  let N₂ := MazurTorsion.Kubert.orderSevenVeluDifferentialNumerator d x₂
  let F := MazurTorsion.Kubert.orderSevenVeluXNumerator d x
  let F₂ := MazurTorsion.Kubert.orderSevenVeluXNumerator d x₂
  let PhiT := MazurTorsion.Doubling.xNumeratorHomogeneous Wq F (K ^ 2)
  let R := MazurTorsion.Doubling.completedYNumerator W x
  let RT := MazurTorsion.Doubling.completedYNumeratorHomogeneous Wq F (K ^ 2)
  have hK : K ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hx0 (sub_ne_zero.mpr hxb))
      (sub_ne_zero.mpr hxc)
  have hK₂ : K₂ ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hx0₂ (sub_ne_zero.mpr hxb₂))
      (sub_ne_zero.mpr hxc₂)
  have hV : V ≠ 0 := by
    intro hV
    apply hy
    simp only [W, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.toAffine]
    linarith
  have hH_eq : H = V ^ 2 := by
    exact MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Doubling.completedCubic_eq_completedY_sq W hP.1
  have hH : H ≠ 0 := by
    rw [hH_eq]
    exact pow_ne_zero 2 hV
  have hp : p = x₂ * H := by
    exact (MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Doubling.addX_self_mul_completedCubic W hP.1 hV).symm
  have hkernel : K₂ * H ^ 3 = K * N := by
    exact MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.kernelPolynomial_at_double hp
      (MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSeven_kernel_double_certificate d x)
  have hN : N ≠ 0 := by
    intro hN
    have hleft : K₂ * H ^ 3 ≠ 0 :=
      mul_ne_zero hK₂ (pow_ne_zero 3 hH)
    apply hleft
    rw [hkernel, hN, mul_zero]
  have hsourceY : V ^ 3 * V₂ = R := by
    exact MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Doubling.completedY_add_self W hP.1 hV
  have hhomX : F₂ * H ^ 7 = PhiT := by
    exact MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenVeluX_double_homogeneous_of_abscissa d x x₂ hp
  have hhomY : N₂ * H ^ 9 * R = RT := by
    exact MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenVeluDifferential_double_homogeneous_of_abscissa
      d x x₂ hp hK hN
  have hquotX :
      F₂ / K₂ ^ 2 =
        (PhiT / K ^ 8) / ((N / K ^ 3) ^ 2 * H) :=
    MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.quotient_doubleX_of_homogeneous hH hK hN hK₂ hkernel hhomX
  have hquotY :
      (N₂ / K₂ ^ 3) * V₂ =
        (RT / K ^ 12) / ((N / K ^ 3 * V) ^ 3) :=
    MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.quotient_doubleCompletedY_of_homogeneous hV hK hN hK₂
      hH_eq hsourceY hkernel hhomY
  have hxMap : X = F / K ^ 2 := by
    exact MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenVeluX_eq_div hx0 hxb hxc
  have hxMap₂ : MazurTorsion.Kubert.orderSevenVeluX d x₂ = F₂ / K₂ ^ 2 := by
    exact MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenVeluX_eq_div hx0₂ hxb₂ hxc₂
  have hdiff : MazurTorsion.Kubert.orderSevenVeluDifferential d x = N / K ^ 3 := by
    exact MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenVeluDifferential_eq_div hx0 hxb hxc
  have hdiff₂ : MazurTorsion.Kubert.orderSevenVeluDifferential d x₂ = N₂ / K₂ ^ 3 := by
    exact MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenVeluDifferential_eq_div hx0₂ hxb₂ hxc₂
  have hcurveImage : Wq.toAffine.Equation X Y := by
    exact MazurTorsion.Kubert.orderSevenVelu_equation hP.1 hx0 hxb hxc
  have himageV : 2 * Y + Wq.a₁ * X + Wq.a₃ = N / K ^ 3 * V := by
    calc
      2 * Y + Wq.a₁ * X + Wq.a₃ =
          MazurTorsion.Kubert.orderSevenVeluDifferential d x * V :=
        MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenVelu_completedY d x y
      _ = N / K ^ 3 * V := by rw [hdiff]
  have himageV_ne : 2 * Y + Wq.a₁ * X + Wq.a₃ ≠ 0 := by
    rw [himageV]
    exact mul_ne_zero (div_ne_zero hN (pow_ne_zero 3 hK)) hV
  have htargetH :
      MazurTorsion.Doubling.completedCubic Wq X = (N / K ^ 3) ^ 2 * H := by
    have hsquare := MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenVelu_completedSquare hx0 hxb hxc
    change MazurTorsion.Kubert.orderSevenVeluDifferential d x ^ 2 * H =
      MazurTorsion.Doubling.completedCubic Wq X at hsquare
    rw [hdiff] at hsquare
    exact hsquare.symm
  have htargetH_ne : (N / K ^ 3) ^ 2 * H ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 (div_ne_zero hN (pow_ne_zero 3 hK))) hH
  have htargetNumerator :
      MazurTorsion.Doubling.xNumerator Wq X = PhiT / K ^ 8 := by
    rw [hxMap]
    exact MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.xNumerator_div_square Wq hK
  have htargetCompletedYNumerator :
      MazurTorsion.Doubling.completedYNumerator Wq X = RT / K ^ 12 := by
    rw [hxMap]
    exact MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.completedYNumerator_div_square Wq hK
  have htargetXmul :
      X₂ * MazurTorsion.Doubling.completedCubic Wq X =
        MazurTorsion.Doubling.xNumerator Wq X := by
    exact MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Doubling.addX_self_mul_completedCubic Wq hcurveImage himageV_ne
  have htargetX :
      X₂ = (PhiT / K ^ 8) / ((N / K ^ 3) ^ 2 * H) := by
    apply (eq_div_iff htargetH_ne).2
    calc
      X₂ * ((N / K ^ 3) ^ 2 * H) =
          X₂ * MazurTorsion.Doubling.completedCubic Wq X := by rw [htargetH]
      _ = MazurTorsion.Doubling.xNumerator Wq X := htargetXmul
      _ = PhiT / K ^ 8 := htargetNumerator
  have htargetYmul :
      (2 * Y + Wq.a₁ * X + Wq.a₃) ^ 3 *
          (2 * Y₂ + Wq.a₁ * X₂ + Wq.a₃) =
        MazurTorsion.Doubling.completedYNumerator Wq X := by
    exact MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Doubling.completedY_add_self Wq hcurveImage himageV_ne
  have htargetY :
      2 * Y₂ + Wq.a₁ * X₂ + Wq.a₃ =
        (RT / K ^ 12) / ((N / K ^ 3 * V) ^ 3) := by
    apply (eq_div_iff (pow_ne_zero 3
      (mul_ne_zero (div_ne_zero hN (pow_ne_zero 3 hK)) hV))).2
    calc
      (2 * Y₂ + Wq.a₁ * X₂ + Wq.a₃) *
          (N / K ^ 3 * V) ^ 3 =
        (2 * Y + Wq.a₁ * X + Wq.a₃) ^ 3 *
          (2 * Y₂ + Wq.a₁ * X₂ + Wq.a₃) := by
            rw [himageV]
            ring
      _ = MazurTorsion.Doubling.completedYNumerator Wq X := htargetYmul
      _ = RT / K ^ 12 := htargetCompletedYNumerator
  constructor
  · calc
      MazurTorsion.Kubert.orderSevenVeluX d x₂ = F₂ / K₂ ^ 2 := hxMap₂
      _ = (PhiT / K ^ 8) / ((N / K ^ 3) ^ 2 * H) := hquotX
      _ = X₂ := htargetX.symm
  · calc
      2 * MazurTorsion.Kubert.orderSevenVeluY d x₂ y₂ +
          Wq.a₁ * MazurTorsion.Kubert.orderSevenVeluX d x₂ + Wq.a₃ =
        MazurTorsion.Kubert.orderSevenVeluDifferential d x₂ * V₂ :=
          MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenVelu_completedY d x₂ y₂
      _ = (N₂ / K₂ ^ 3) * V₂ := by rw [hdiff₂]
      _ = (RT / K ^ 12) / ((N / K ^ 3 * V) ^ 3) := hquotY
      _ = 2 * Y₂ + Wq.a₁ * X₂ + Wq.a₃ := htargetY.symm













end MazurTorsion.Kubert

end MazurTransfer.Order49DoublingCoordinateConsumers

theorem solution {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (horder : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49) :
    MazurTorsion.Kubert.OrderSevenDoublingCoordinates d x y := by
  apply MazurTransfer.Order49DoublingCoordinateConsumers.MazurTorsion.Kubert.orderSevenVelu_double_coordinates <;> assumption
#print axioms solution
