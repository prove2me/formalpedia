-- Prove2me | solution 1 for MazurTransfer.order49_doubling_geometry_orderSevenVeluX_double_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T03:58:00.223361+00:00
-- url     : https://prove2.me/submissions/4e11cb64-8f5a-4919-92c3-5dfd23f579ec

import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49DoublingCoordinateFormulas
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
import Mathlib
import Theorems.Thm_MazurTransfer_order49_doubling_polynomial_identity
open Polynomial
theorem MazurTransfer.Order49DoublingGeometryHelpers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.polynomial_identity (d : ℚ) :
    MazurTorsion.Kubert.OrderSevenDoublingCertificate.veluXHomogeneousPolynomial d (MazurTorsion.Kubert.OrderSevenDoublingCertificate.sourceDoubleXPolynomial d)
        (MazurTorsion.Kubert.OrderSevenDoublingCertificate.sourceCompletedCubicPolynomial d) =
      MazurTorsion.Kubert.OrderSevenDoublingCertificate.doubleXHomogeneousPolynomial (MazurTorsion.Kubert.orderSevenQuotient d)
        (MazurTorsion.Kubert.OrderSevenDoublingCertificate.veluXPolynomial d) (MazurTorsion.Kubert.OrderSevenDoublingCertificate.kernelPolynomial d ^ 2) := by
  apply MazurTransfer.order49_doubling_polynomial_identity <;> assumption
namespace MazurTransfer.Order49DoublingGeometryHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenIsogenyPolynomialData





@[simp] theorem kernelPolynomial_eval (d x : ℚ) :
    (MazurTorsion.Kubert.OrderSevenIsogenyPolynomialData.kernelPolynomial d).eval x = MazurTorsion.Kubert.orderSevenKernelPolynomial d x := by
  simp [MazurTorsion.Kubert.OrderSevenIsogenyPolynomialData.kernelPolynomial, MazurTorsion.Kubert.orderSevenKernelPolynomial]

@[simp] theorem veluXPolynomial_eval (d x : ℚ) :
    (MazurTorsion.Kubert.OrderSevenIsogenyPolynomialData.veluXPolynomial d).eval x = MazurTorsion.Kubert.orderSevenVeluXNumerator d x := by
  simp [MazurTorsion.Kubert.OrderSevenIsogenyPolynomialData.veluXPolynomial, MazurTorsion.Kubert.orderSevenVeluXNumerator]

end MazurTorsion.Kubert.OrderSevenIsogenyPolynomialData

end MazurTransfer.Order49DoublingGeometryHelpers

namespace MazurTransfer.Order49DoublingGeometryHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert





















private theorem orderSevenVeluX_double_homogeneous (d x : ℚ) :
    MazurTorsion.Kubert.orderSevenVeluXNumeratorHomogeneous d
        (MazurTorsion.Doubling.xNumerator (MazurTorsion.Kubert.orderSevenFamily d) x)
        (MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x) =
      MazurTorsion.Doubling.xNumeratorHomogeneous (MazurTorsion.Kubert.orderSevenQuotient d)
        (MazurTorsion.Kubert.orderSevenVeluXNumerator d x)
        (MazurTorsion.Kubert.orderSevenKernelPolynomial d x ^ 2) := by
  have h := congrArg (Polynomial.eval x) (MazurTransfer.Order49DoublingGeometryHelpers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.polynomial_identity d)
  simpa only [MazurTorsion.Kubert.OrderSevenDoublingCertificate.veluXHomogeneousPolynomial,
    MazurTorsion.Kubert.OrderSevenDoublingCertificate.sourceDoubleXPolynomial,
    MazurTorsion.Kubert.OrderSevenDoublingCertificate.sourceCompletedCubicPolynomial,
    MazurTorsion.Kubert.OrderSevenDoublingCertificate.doubleXHomogeneousPolynomial,
    MazurTorsion.Kubert.OrderSevenDoublingCertificate.veluXPolynomial,
    MazurTorsion.Kubert.OrderSevenDoublingCertificate.kernelPolynomial,
    MazurTorsion.Kubert.orderSevenVeluXNumeratorHomogeneous,
    MazurTorsion.Kubert.orderSevenVeluXNumerator,
    MazurTorsion.Kubert.orderSevenKernelPolynomial,
    MazurTorsion.Doubling.xNumerator,
    MazurTorsion.Doubling.completedCubic,
    MazurTorsion.Doubling.xNumeratorHomogeneous,
    MazurTransfer.Order49DoublingGeometryHelpers.MazurTorsion.Kubert.OrderSevenIsogenyPolynomialData.kernelPolynomial_eval,
    MazurTransfer.Order49DoublingGeometryHelpers.MazurTorsion.Kubert.OrderSevenIsogenyPolynomialData.veluXPolynomial_eval,
    Polynomial.eval_add,
    Polynomial.eval_sub,
    Polynomial.eval_mul,
    Polynomial.eval_pow,
    Polynomial.eval_C,
    Polynomial.eval_X,
    Polynomial.eval_one,
    Polynomial.eval_zero,
    Polynomial.eval_ofNat,
    Polynomial.eval_natCast,
    Polynomial.coe_evalRingHom,
    map_add,
    map_sub,
    map_mul,
    map_pow,
    map_ofNat,
    map_natCast,
    one_pow,
    mul_one,
    one_mul] using h













































end MazurTorsion.Kubert

end MazurTransfer.Order49DoublingGeometryHelpers

theorem solution (d x : ℚ) :
    MazurTorsion.Kubert.orderSevenVeluXNumeratorHomogeneous d
        (MazurTorsion.Doubling.xNumerator (MazurTorsion.Kubert.orderSevenFamily d) x)
        (MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x) =
      MazurTorsion.Doubling.xNumeratorHomogeneous (MazurTorsion.Kubert.orderSevenQuotient d)
        (MazurTorsion.Kubert.orderSevenVeluXNumerator d x)
        (MazurTorsion.Kubert.orderSevenKernelPolynomial d x ^ 2) := by
  apply MazurTransfer.Order49DoublingGeometryHelpers.MazurTorsion.Kubert.orderSevenVeluX_double_homogeneous <;> assumption
#print axioms solution
