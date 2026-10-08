-- Prove2me | solution 1 for MazurTransfer.order49_doubling_polynomial_identity
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T02:43:27.828708+00:00
-- url     : https://prove2.me/submissions/3c9b436b-1fed-4626-88c6-bdee3c696379

import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49DirectEvaluationPredicates
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Theorems.Thm_MazurTransfer_order49_doubling_eval_block_0
import Theorems.Thm_MazurTransfer_order49_doubling_eval_block_1
import Theorems.Thm_MazurTransfer_order49_doubling_eval_block_2
import Theorems.Thm_MazurTransfer_order49_doubling_eval_block_3
import Theorems.Thm_MazurTransfer_order49_doubling_eval_block_4
import Theorems.Thm_MazurTransfer_order49_doubling_eval_block_5
import Theorems.Thm_MazurTransfer_order49_doubling_eval_block_6
import Theorems.Thm_MazurTransfer_order49_doubling_eval_block_7
open Polynomial
theorem MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock0 (d : ℚ) (i : Fin 4) :
    MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.EvalCertificate d ((i : ℚ) + 0) := by
  exact MazurTransfer.order49_doubling_eval_block_0 d i

theorem MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock1 (d : ℚ) (i : Fin 4) :
    MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.EvalCertificate d ((i : ℚ) + 4) := by
  exact MazurTransfer.order49_doubling_eval_block_1 d i

theorem MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock2 (d : ℚ) (i : Fin 4) :
    MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.EvalCertificate d ((i : ℚ) + 8) := by
  exact MazurTransfer.order49_doubling_eval_block_2 d i

theorem MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock3 (d : ℚ) (i : Fin 4) :
    MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.EvalCertificate d ((i : ℚ) + 12) := by
  exact MazurTransfer.order49_doubling_eval_block_3 d i

theorem MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock4 (d : ℚ) (i : Fin 4) :
    MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.EvalCertificate d ((i : ℚ) + 16) := by
  exact MazurTransfer.order49_doubling_eval_block_4 d i

theorem MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock5 (d : ℚ) (i : Fin 4) :
    MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.EvalCertificate d ((i : ℚ) + 20) := by
  exact MazurTransfer.order49_doubling_eval_block_5 d i

theorem MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock6 (d : ℚ) (i : Fin 4) :
    MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.EvalCertificate d ((i : ℚ) + 24) := by
  exact MazurTransfer.order49_doubling_eval_block_6 d i

theorem MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock7 (d : ℚ) (i : Fin 1) :
    MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.EvalCertificate d ((i : ℚ) + 28) := by
  exact MazurTransfer.order49_doubling_eval_block_7 d i
namespace MazurTransfer.Order49ArithmeticAggregateConsumers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenDoublingCertificate













namespace Internal

lemma left_degree (d : ℚ) :
    (MazurTorsion.Kubert.OrderSevenDoublingCertificate.veluXHomogeneousPolynomial d (MazurTorsion.Kubert.OrderSevenDoublingCertificate.sourceDoubleXPolynomial d)
      (MazurTorsion.Kubert.OrderSevenDoublingCertificate.sourceCompletedCubicPolynomial d)).natDegree ≤ 28 := by
  unfold MazurTorsion.Kubert.OrderSevenDoublingCertificate.veluXHomogeneousPolynomial MazurTorsion.Kubert.OrderSevenDoublingCertificate.sourceDoubleXPolynomial
    MazurTorsion.Kubert.OrderSevenDoublingCertificate.sourceCompletedCubicPolynomial
  compute_degree

lemma right_degree (d : ℚ) :
    (MazurTorsion.Kubert.OrderSevenDoublingCertificate.doubleXHomogeneousPolynomial (MazurTorsion.Kubert.orderSevenQuotient d)
      (MazurTorsion.Kubert.OrderSevenDoublingCertificate.veluXPolynomial d) (MazurTorsion.Kubert.OrderSevenDoublingCertificate.kernelPolynomial d ^ 2)).natDegree ≤ 28 := by
  unfold MazurTorsion.Kubert.OrderSevenDoublingCertificate.doubleXHomogeneousPolynomial MazurTorsion.Kubert.OrderSevenDoublingCertificate.veluXPolynomial MazurTorsion.Kubert.OrderSevenDoublingCertificate.kernelPolynomial
    MazurTorsion.Kubert.OrderSevenIsogenyPolynomialData.veluXPolynomial
    MazurTorsion.Kubert.OrderSevenIsogenyPolynomialData.kernelPolynomial
  compute_degree



end Internal

end MazurTorsion.Kubert.OrderSevenDoublingCertificate

end MazurTransfer.Order49ArithmeticAggregateConsumers

namespace MazurTransfer.Order49ArithmeticAggregateConsumers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenDoublingCertificate

private theorem eval_fin (d : ℚ) (i : Fin 29) :
    MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.EvalCertificate d (i : ℚ) := by
  fin_cases i
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock0 d (0 : Fin 4) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock0 d (1 : Fin 4) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock0 d (2 : Fin 4) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock0 d (3 : Fin 4) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock1 d (0 : Fin 4) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock1 d (1 : Fin 4) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock1 d (2 : Fin 4) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock1 d (3 : Fin 4) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock2 d (0 : Fin 4) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock2 d (1 : Fin 4) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock2 d (2 : Fin 4) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock2 d (3 : Fin 4) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock3 d (0 : Fin 4) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock3 d (1 : Fin 4) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock3 d (2 : Fin 4) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock3 d (3 : Fin 4) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock4 d (0 : Fin 4) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock4 d (1 : Fin 4) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock4 d (2 : Fin 4) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock4 d (3 : Fin 4) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock5 d (0 : Fin 4) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock5 d (1 : Fin 4) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock5 d (2 : Fin 4) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock5 d (3 : Fin 4) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock6 d (0 : Fin 4) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock6 d (1 : Fin 4) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock6 d (2 : Fin 4) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock6 d (3 : Fin 4) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock7 d (0 : Fin 1) using 1; norm_num)

/-- The degree-`28` homogeneous abscissa certificate for doubling through
the explicit order-seven Vélu map. -/
theorem polynomial_identity (d : ℚ) :
    MazurTorsion.Kubert.OrderSevenDoublingCertificate.veluXHomogeneousPolynomial d (MazurTorsion.Kubert.OrderSevenDoublingCertificate.sourceDoubleXPolynomial d)
        (MazurTorsion.Kubert.OrderSevenDoublingCertificate.sourceCompletedCubicPolynomial d) =
      MazurTorsion.Kubert.OrderSevenDoublingCertificate.doubleXHomogeneousPolynomial (MazurTorsion.Kubert.orderSevenQuotient d)
        (MazurTorsion.Kubert.OrderSevenDoublingCertificate.veluXPolynomial d) (MazurTorsion.Kubert.OrderSevenDoublingCertificate.kernelPolynomial d ^ 2) := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    _ _ (f := fun i : Fin 29 ↦ (i : ℚ))
  · intro i j hij
    apply Fin.ext
    exact Nat.cast_injective hij
  · intro i
    exact MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.eval_fin d i
  · simp only [Fintype.card_fin]
    have hl := MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.left_degree d
    have hr := MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.right_degree d
    omega

end MazurTorsion.Kubert.OrderSevenDoublingCertificate

end MazurTransfer.Order49ArithmeticAggregateConsumers

theorem solution (d : ℚ) :
    MazurTorsion.Kubert.OrderSevenDoublingCertificate.veluXHomogeneousPolynomial d (MazurTorsion.Kubert.OrderSevenDoublingCertificate.sourceDoubleXPolynomial d)
        (MazurTorsion.Kubert.OrderSevenDoublingCertificate.sourceCompletedCubicPolynomial d) =
      MazurTorsion.Kubert.OrderSevenDoublingCertificate.doubleXHomogeneousPolynomial (MazurTorsion.Kubert.orderSevenQuotient d)
        (MazurTorsion.Kubert.OrderSevenDoublingCertificate.veluXPolynomial d) (MazurTorsion.Kubert.OrderSevenDoublingCertificate.kernelPolynomial d ^ 2) := by
  exact MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.polynomial_identity d
#print axioms solution
