-- Prove2me | solution 1 for MazurTransfer.order49_doubling_eval_block_0
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T02:41:43.567023+00:00
-- url     : https://prove2.me/submissions/7109d270-6e18-4541-825a-63437ea216c1

import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49DirectEvaluationPredicates
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
open Polynomial
namespace MazurTransfer.Order49ArithmeticAggregateStandalone
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/




open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert










































/-- The kernel polynomial whose roots are the three affine pole
abscissae. -/
@[expose] def orderSevenKernelPolynomial (d x : ℚ) : ℚ :=
  x * (x - MazurTorsion.Kubert.orderSevenB d) * (x - MazurTorsion.Kubert.orderSevenC d)

/-- The cleared numerator of `orderSevenVeluX`; its denominator is the
square of `orderSevenKernelPolynomial`. -/
@[expose] def orderSevenVeluXNumerator (d x : ℚ) : ℚ :=
  x ^ 7 - 2 * d * (d - 1) * (d + 1) * x ^ 6 +
    d * (d - 1) *
      (d ^ 5 + 2 * d ^ 4 - 3 * d ^ 3 + 5 * d ^ 2 - 7 * d + 1) *
        x ^ 5 -
    d ^ 3 * (d - 1) ^ 2 *
      (6 * d ^ 4 - 9 * d ^ 3 + 12 * d ^ 2 - 13 * d - 1) * x ^ 4 +
    d ^ 4 * (d - 1) ^ 3 *
      (d ^ 5 + d ^ 4 + 4 * d ^ 3 - 8 * d ^ 2 - 7 * d - 1) * x ^ 3 -
    d ^ 6 * (d - 1) ^ 4 * (d + 1) *
      (3 * d ^ 2 - 5 * d - 3) * x ^ 2 +
    d ^ 8 * (d - 1) ^ 5 * (d ^ 2 - 3 * d - 3) * x +
    d ^ 10 * (d - 1) ^ 6























































































end MazurTorsion.Kubert

end MazurTransfer.Order49ArithmeticAggregateStandalone

namespace MazurTransfer.Order49ArithmeticAggregateStandalone
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenDoublingCertificate













namespace Internal





def EvalCertificate (d n : ℚ) : Prop :=
  (MazurTorsion.Kubert.OrderSevenDoublingCertificate.veluXHomogeneousPolynomial d (MazurTorsion.Kubert.OrderSevenDoublingCertificate.sourceDoubleXPolynomial d)
    (MazurTorsion.Kubert.OrderSevenDoublingCertificate.sourceCompletedCubicPolynomial d)).eval n =
  (MazurTorsion.Kubert.OrderSevenDoublingCertificate.doubleXHomogeneousPolynomial (MazurTorsion.Kubert.orderSevenQuotient d)
    (MazurTorsion.Kubert.OrderSevenDoublingCertificate.veluXPolynomial d) (MazurTorsion.Kubert.OrderSevenDoublingCertificate.kernelPolynomial d ^ 2)).eval n

end Internal

end MazurTorsion.Kubert.OrderSevenDoublingCertificate

end MazurTransfer.Order49ArithmeticAggregateStandalone

namespace MazurTransfer.Order49ArithmeticAggregateStandalone
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenIsogenyPolynomialData





@[simp] theorem kernelPolynomial_eval (d x : ℚ) :
    (MazurTorsion.Kubert.OrderSevenIsogenyPolynomialData.kernelPolynomial d).eval x = MazurTransfer.Order49ArithmeticAggregateStandalone.MazurTorsion.Kubert.orderSevenKernelPolynomial d x := by
  simp [MazurTorsion.Kubert.OrderSevenIsogenyPolynomialData.kernelPolynomial, MazurTransfer.Order49ArithmeticAggregateStandalone.MazurTorsion.Kubert.orderSevenKernelPolynomial]

@[simp] theorem veluXPolynomial_eval (d x : ℚ) :
    (MazurTorsion.Kubert.OrderSevenIsogenyPolynomialData.veluXPolynomial d).eval x = MazurTransfer.Order49ArithmeticAggregateStandalone.MazurTorsion.Kubert.orderSevenVeluXNumerator d x := by
  simp [MazurTorsion.Kubert.OrderSevenIsogenyPolynomialData.veluXPolynomial, MazurTransfer.Order49ArithmeticAggregateStandalone.MazurTorsion.Kubert.orderSevenVeluXNumerator]

end MazurTorsion.Kubert.OrderSevenIsogenyPolynomialData

end MazurTransfer.Order49ArithmeticAggregateStandalone

namespace MazurTransfer.Order49ArithmeticAggregateStandalone
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



namespace MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal



private lemma eval_0 (d : ℚ) : MazurTransfer.Order49ArithmeticAggregateStandalone.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.EvalCertificate d 0 := by
   (  simp  [  MazurTransfer.Order49ArithmeticAggregateStandalone.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.EvalCertificate  ,  MazurTorsion.Kubert.OrderSevenDoublingCertificate.veluXHomogeneousPolynomial  ,  MazurTorsion.Kubert.OrderSevenDoublingCertificate.sourceDoubleXPolynomial  ,  MazurTorsion.Kubert.OrderSevenDoublingCertificate.sourceCompletedCubicPolynomial  ,  MazurTorsion.Kubert.OrderSevenDoublingCertificate.doubleXHomogeneousPolynomial  ,  MazurTorsion.Kubert.OrderSevenDoublingCertificate.veluXPolynomial  ,  MazurTorsion.Kubert.OrderSevenDoublingCertificate.kernelPolynomial  ,  MazurTransfer.Order49ArithmeticAggregateStandalone.MazurTorsion.Kubert.orderSevenVeluXNumerator  ,  MazurTransfer.Order49ArithmeticAggregateStandalone.MazurTorsion.Kubert.orderSevenKernelPolynomial  ,  MazurTorsion.Kubert.orderSevenFamily  ,  MazurTorsion.Kubert.orderSevenQuotient  ,  MazurTorsion.Kubert.orderSevenB  ,  MazurTorsion.Kubert.orderSevenC  ,  MazurTorsion.Kubert.tateNormalCurve  ,  WeierstrassCurve.b₂  ,  WeierstrassCurve.b₄  ,  WeierstrassCurve.b₆  ,  WeierstrassCurve.b₈  ]  <;>  ring  ) 

private lemma eval_1 (d : ℚ) : MazurTransfer.Order49ArithmeticAggregateStandalone.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.EvalCertificate d 1 := by
   (  simp  [  MazurTransfer.Order49ArithmeticAggregateStandalone.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.EvalCertificate  ,  MazurTorsion.Kubert.OrderSevenDoublingCertificate.veluXHomogeneousPolynomial  ,  MazurTorsion.Kubert.OrderSevenDoublingCertificate.sourceDoubleXPolynomial  ,  MazurTorsion.Kubert.OrderSevenDoublingCertificate.sourceCompletedCubicPolynomial  ,  MazurTorsion.Kubert.OrderSevenDoublingCertificate.doubleXHomogeneousPolynomial  ,  MazurTorsion.Kubert.OrderSevenDoublingCertificate.veluXPolynomial  ,  MazurTorsion.Kubert.OrderSevenDoublingCertificate.kernelPolynomial  ,  MazurTransfer.Order49ArithmeticAggregateStandalone.MazurTorsion.Kubert.orderSevenVeluXNumerator  ,  MazurTransfer.Order49ArithmeticAggregateStandalone.MazurTorsion.Kubert.orderSevenKernelPolynomial  ,  MazurTorsion.Kubert.orderSevenFamily  ,  MazurTorsion.Kubert.orderSevenQuotient  ,  MazurTorsion.Kubert.orderSevenB  ,  MazurTorsion.Kubert.orderSevenC  ,  MazurTorsion.Kubert.tateNormalCurve  ,  WeierstrassCurve.b₂  ,  WeierstrassCurve.b₄  ,  WeierstrassCurve.b₆  ,  WeierstrassCurve.b₈  ]  <;>  ring  ) 

private lemma eval_2 (d : ℚ) : MazurTransfer.Order49ArithmeticAggregateStandalone.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.EvalCertificate d 2 := by
   (  simp  [  MazurTransfer.Order49ArithmeticAggregateStandalone.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.EvalCertificate  ,  MazurTorsion.Kubert.OrderSevenDoublingCertificate.veluXHomogeneousPolynomial  ,  MazurTorsion.Kubert.OrderSevenDoublingCertificate.sourceDoubleXPolynomial  ,  MazurTorsion.Kubert.OrderSevenDoublingCertificate.sourceCompletedCubicPolynomial  ,  MazurTorsion.Kubert.OrderSevenDoublingCertificate.doubleXHomogeneousPolynomial  ,  MazurTorsion.Kubert.OrderSevenDoublingCertificate.veluXPolynomial  ,  MazurTorsion.Kubert.OrderSevenDoublingCertificate.kernelPolynomial  ,  MazurTransfer.Order49ArithmeticAggregateStandalone.MazurTorsion.Kubert.orderSevenVeluXNumerator  ,  MazurTransfer.Order49ArithmeticAggregateStandalone.MazurTorsion.Kubert.orderSevenKernelPolynomial  ,  MazurTorsion.Kubert.orderSevenFamily  ,  MazurTorsion.Kubert.orderSevenQuotient  ,  MazurTorsion.Kubert.orderSevenB  ,  MazurTorsion.Kubert.orderSevenC  ,  MazurTorsion.Kubert.tateNormalCurve  ,  WeierstrassCurve.b₂  ,  WeierstrassCurve.b₄  ,  WeierstrassCurve.b₆  ,  WeierstrassCurve.b₈  ]  <;>  ring  ) 

private lemma eval_3 (d : ℚ) : MazurTransfer.Order49ArithmeticAggregateStandalone.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.EvalCertificate d 3 := by
   (  simp  [  MazurTransfer.Order49ArithmeticAggregateStandalone.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.EvalCertificate  ,  MazurTorsion.Kubert.OrderSevenDoublingCertificate.veluXHomogeneousPolynomial  ,  MazurTorsion.Kubert.OrderSevenDoublingCertificate.sourceDoubleXPolynomial  ,  MazurTorsion.Kubert.OrderSevenDoublingCertificate.sourceCompletedCubicPolynomial  ,  MazurTorsion.Kubert.OrderSevenDoublingCertificate.doubleXHomogeneousPolynomial  ,  MazurTorsion.Kubert.OrderSevenDoublingCertificate.veluXPolynomial  ,  MazurTorsion.Kubert.OrderSevenDoublingCertificate.kernelPolynomial  ,  MazurTransfer.Order49ArithmeticAggregateStandalone.MazurTorsion.Kubert.orderSevenVeluXNumerator  ,  MazurTransfer.Order49ArithmeticAggregateStandalone.MazurTorsion.Kubert.orderSevenKernelPolynomial  ,  MazurTorsion.Kubert.orderSevenFamily  ,  MazurTorsion.Kubert.orderSevenQuotient  ,  MazurTorsion.Kubert.orderSevenB  ,  MazurTorsion.Kubert.orderSevenC  ,  MazurTorsion.Kubert.tateNormalCurve  ,  WeierstrassCurve.b₂  ,  WeierstrassCurve.b₄  ,  WeierstrassCurve.b₆  ,  WeierstrassCurve.b₈  ]  <;>  ring  ) 

theorem evalBlock0 (d : ℚ) (i : Fin 4) :
    MazurTransfer.Order49ArithmeticAggregateStandalone.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.EvalCertificate d ((i : ℚ) + 0) := by
  fin_cases i
  · simpa using MazurTransfer.Order49ArithmeticAggregateStandalone.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.eval_0 d
  · simpa using MazurTransfer.Order49ArithmeticAggregateStandalone.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.eval_1 d
  · simpa using MazurTransfer.Order49ArithmeticAggregateStandalone.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.eval_2 d
  · simpa using MazurTransfer.Order49ArithmeticAggregateStandalone.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.eval_3 d

end MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal

end MazurTransfer.Order49ArithmeticAggregateStandalone

theorem solution (d : ℚ) (i : Fin 4) :
    MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.EvalCertificate d ((i : ℚ) + 0) := by
  exact MazurTransfer.Order49ArithmeticAggregateStandalone.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock0 d i
#print axioms solution
