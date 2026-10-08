-- Prove2me | solution 1 for MazurTransfer.order49_doubling_geometry_derivative_doubleX_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T03:58:09.594596+00:00
-- url     : https://prove2.me/submissions/edb27a6b-786e-463e-a039-4295a3c72f95

import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49DoublingCoordinateFormulas
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
import Mathlib
import Theorems.Thm_MazurTransfer_order49_doubling_geometry_orderSevenVeluX_double_homogeneous
open Polynomial
theorem MazurTransfer.Order49DoublingGeometryHelpers.MazurTorsion.Kubert.orderSevenVeluX_double_homogeneous (d x : ℚ) :
    MazurTorsion.Kubert.orderSevenVeluXNumeratorHomogeneous d
        (MazurTorsion.Doubling.xNumerator (MazurTorsion.Kubert.orderSevenFamily d) x)
        (MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x) =
      MazurTorsion.Doubling.xNumeratorHomogeneous (MazurTorsion.Kubert.orderSevenQuotient d)
        (MazurTorsion.Kubert.orderSevenVeluXNumerator d x)
        (MazurTorsion.Kubert.orderSevenKernelPolynomial d x ^ 2) := by
  apply MazurTransfer.order49_doubling_geometry_orderSevenVeluX_double_homogeneous <;> assumption
namespace MazurTransfer.Order49DoublingGeometryHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



section
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Doubling











/-- Homogenization of `completedCubic` to degree three. -/
def completedCubicHomogeneous
    {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (u v : R) : R :=
  4 * u ^ 3 + W.b₂ * u ^ 2 * v + 2 * W.b₄ * u * v ^ 2 +
    W.b₆ * v ^ 3





@[simp] theorem xNumeratorHomogeneous_at_one
    (W : WeierstrassCurve ℚ) (x : ℚ) :
    MazurTorsion.Doubling.xNumeratorHomogeneous W x 1 = MazurTorsion.Doubling.xNumerator W x := by
  simp only [MazurTorsion.Doubling.xNumeratorHomogeneous, MazurTorsion.Doubling.xNumerator]
  ring



@[simp] theorem completedCubicHomogeneous_at_one
    (W : WeierstrassCurve ℚ) (x : ℚ) :
    MazurTransfer.Order49DoublingGeometryHelpers.MazurTorsion.Doubling.completedCubicHomogeneous W x 1 = MazurTorsion.Doubling.completedCubic W x := by
  simp only [MazurTransfer.Order49DoublingGeometryHelpers.MazurTorsion.Doubling.completedCubicHomogeneous, MazurTorsion.Doubling.completedCubic]
  ring









end MazurTorsion.Doubling

end
end MazurTransfer.Order49DoublingGeometryHelpers

namespace MazurTransfer.Order49DoublingGeometryHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenDoublingDerivative

/-- A monic degree-seven binary form, written with its seven lower
coefficients. -/
def veluXHomogeneous
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ u v : ℚ) : ℚ :=
  u ^ 7 + a₆ * u ^ 6 * v + a₅ * u ^ 5 * v ^ 2 +
    a₄ * u ^ 4 * v ^ 3 + a₃ * u ^ 3 * v ^ 4 +
    a₂ * u ^ 2 * v ^ 5 + a₁ * u * v ^ 6 + a₀ * v ^ 7



/-- Homogenization of the cubic denominator `X (X - b) (X - c)`. -/
def kernelHomogeneous (b c u v : ℚ) : ℚ :=
  u * (u - b * v) * (u - c * v)





















theorem eval_completedCubicPolynomial
    (W : WeierstrassCurve ℚ) (u v : ℚ[X]) (x : ℚ) :
    (MazurTorsion.Kubert.OrderSevenDoublingDerivative.completedCubicPolynomial W u v).eval x =
      MazurTransfer.Order49DoublingGeometryHelpers.MazurTorsion.Doubling.completedCubicHomogeneous W (u.eval x) (v.eval x) := by
  simp [MazurTorsion.Kubert.OrderSevenDoublingDerivative.completedCubicPolynomial, MazurTransfer.Order49DoublingGeometryHelpers.MazurTorsion.Doubling.completedCubicHomogeneous]



theorem eval_doubleXPolynomial
    (W : WeierstrassCurve ℚ) (u v : ℚ[X]) (x : ℚ) :
    (MazurTorsion.Kubert.OrderSevenDoublingDerivative.doubleXPolynomial W u v).eval x =
      MazurTorsion.Doubling.xNumeratorHomogeneous W (u.eval x) (v.eval x) := by
  simp [MazurTorsion.Kubert.OrderSevenDoublingDerivative.doubleXPolynomial, MazurTorsion.Doubling.xNumeratorHomogeneous]





theorem eval_veluXPolynomial
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ : ℚ) (u v : ℚ[X]) (x : ℚ) :
    (MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXPolynomial a₆ a₅ a₄ a₃ a₂ a₁ a₀ u v).eval x =
      MazurTransfer.Order49DoublingGeometryHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneous a₆ a₅ a₄ a₃ a₂ a₁ a₀ (u.eval x) (v.eval x) := by
  simp [MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXPolynomial, MazurTransfer.Order49DoublingGeometryHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneous]



theorem eval_kernelPolynomial
    (b c : ℚ) (u v : ℚ[X]) (x : ℚ) :
    (MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelPolynomial b c u v).eval x =
      MazurTransfer.Order49DoublingGeometryHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneous b c (u.eval x) (v.eval x) := by
  simp [MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelPolynomial, MazurTransfer.Order49DoublingGeometryHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneous]







































end MazurTorsion.Kubert.OrderSevenDoublingDerivative

end MazurTransfer.Order49DoublingGeometryHelpers

namespace MazurTransfer.Order49DoublingGeometryHelpers
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



private theorem derivativeVeluXHomogeneous_eq
    (d u v : ℚ) :
    MazurTransfer.Order49DoublingGeometryHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneous
        (MazurTorsion.Kubert.orderSevenVeluA6 d) (MazurTorsion.Kubert.orderSevenVeluA5 d)
        (MazurTorsion.Kubert.orderSevenVeluA4 d) (MazurTorsion.Kubert.orderSevenVeluA3 d)
        (MazurTorsion.Kubert.orderSevenVeluA2 d) (MazurTorsion.Kubert.orderSevenVeluA1 d)
        (MazurTorsion.Kubert.orderSevenVeluA0 d) u v =
      MazurTorsion.Kubert.orderSevenVeluXNumeratorHomogeneous d u v := by
  simp only [MazurTransfer.Order49DoublingGeometryHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneous,
    MazurTorsion.Kubert.orderSevenVeluXNumeratorHomogeneous, MazurTorsion.Kubert.orderSevenVeluA6,
    MazurTorsion.Kubert.orderSevenVeluA5, MazurTorsion.Kubert.orderSevenVeluA4, MazurTorsion.Kubert.orderSevenVeluA3,
    MazurTorsion.Kubert.orderSevenVeluA2, MazurTorsion.Kubert.orderSevenVeluA1, MazurTorsion.Kubert.orderSevenVeluA0,
    MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₆,
    MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₅,
    MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₄,
    MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₃,
    MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₂,
    MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₁,
    MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₀]
  ring





private theorem derivative_doubleX_certificate (d : ℚ) :
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.composedVeluX
        (MazurTorsion.Kubert.orderSevenVeluA6 d) (MazurTorsion.Kubert.orderSevenVeluA5 d)
        (MazurTorsion.Kubert.orderSevenVeluA4 d) (MazurTorsion.Kubert.orderSevenVeluA3 d)
        (MazurTorsion.Kubert.orderSevenVeluA2 d) (MazurTorsion.Kubert.orderSevenVeluA1 d)
        (MazurTorsion.Kubert.orderSevenVeluA0 d) (MazurTorsion.Kubert.orderSevenFamily d) =
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.targetDoubleX
        (MazurTorsion.Kubert.orderSevenQuotient d)
        (MazurTorsion.Kubert.orderSevenVeluA6 d) (MazurTorsion.Kubert.orderSevenVeluA5 d)
        (MazurTorsion.Kubert.orderSevenVeluA4 d) (MazurTorsion.Kubert.orderSevenVeluA3 d)
        (MazurTorsion.Kubert.orderSevenVeluA2 d) (MazurTorsion.Kubert.orderSevenVeluA1 d)
        (MazurTorsion.Kubert.orderSevenVeluA0 d) (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) := by
  apply Polynomial.funext
  intro x
  have h := MazurTransfer.Order49DoublingGeometryHelpers.MazurTorsion.Kubert.orderSevenVeluX_double_homogeneous d x
  simpa only [MazurTorsion.Kubert.OrderSevenDoublingDerivative.composedVeluX,
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.targetDoubleX,
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.sourceDoubleX,
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.sourceCompletedCubic,
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluX,
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseKernel,
    MazurTransfer.Order49DoublingGeometryHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_veluXPolynomial,
    MazurTransfer.Order49DoublingGeometryHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_doubleXPolynomial,
    MazurTransfer.Order49DoublingGeometryHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_completedCubicPolynomial,
    MazurTransfer.Order49DoublingGeometryHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_kernelPolynomial,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_pow,
    MazurTransfer.Order49DoublingGeometryHelpers.MazurTorsion.Doubling.xNumeratorHomogeneous_at_one,
    MazurTransfer.Order49DoublingGeometryHelpers.MazurTorsion.Doubling.completedCubicHomogeneous_at_one,
    MazurTransfer.Order49DoublingGeometryHelpers.MazurTorsion.Kubert.derivativeVeluXHomogeneous_eq,
    MazurTransfer.Order49DoublingGeometryHelpers.MazurTorsion.Kubert.orderSevenVeluXNumeratorHomogeneous_at_one,
    MazurTransfer.Order49DoublingGeometryHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneous,
    MazurTorsion.Kubert.orderSevenKernelPolynomial, mul_one] using h











































end MazurTorsion.Kubert

end MazurTransfer.Order49DoublingGeometryHelpers

theorem solution (d : ℚ) :
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.composedVeluX
        (MazurTorsion.Kubert.orderSevenVeluA6 d) (MazurTorsion.Kubert.orderSevenVeluA5 d)
        (MazurTorsion.Kubert.orderSevenVeluA4 d) (MazurTorsion.Kubert.orderSevenVeluA3 d)
        (MazurTorsion.Kubert.orderSevenVeluA2 d) (MazurTorsion.Kubert.orderSevenVeluA1 d)
        (MazurTorsion.Kubert.orderSevenVeluA0 d) (MazurTorsion.Kubert.orderSevenFamily d) =
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.targetDoubleX
        (MazurTorsion.Kubert.orderSevenQuotient d)
        (MazurTorsion.Kubert.orderSevenVeluA6 d) (MazurTorsion.Kubert.orderSevenVeluA5 d)
        (MazurTorsion.Kubert.orderSevenVeluA4 d) (MazurTorsion.Kubert.orderSevenVeluA3 d)
        (MazurTorsion.Kubert.orderSevenVeluA2 d) (MazurTorsion.Kubert.orderSevenVeluA1 d)
        (MazurTorsion.Kubert.orderSevenVeluA0 d) (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) := by
  apply MazurTransfer.Order49DoublingGeometryHelpers.MazurTorsion.Kubert.derivative_doubleX_certificate <;> assumption
#print axioms solution
