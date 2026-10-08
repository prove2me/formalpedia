-- Prove2me | solution 1 for MazurTransfer.order49_quotient_prePsi_seven_polynomial_factorization
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T02:46:39.914927+00:00
-- url     : https://prove2.me/submissions/96110186-5cda-41c7-a068-de6611738e5d

import Definitions.Def_MazurTransfer_Order49BacktrackingCofactors
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49DirectEvaluationPredicates
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Theorems.Thm_MazurTransfer_order49_division_eval_block_0
import Theorems.Thm_MazurTransfer_order49_division_eval_block_1
import Theorems.Thm_MazurTransfer_order49_division_eval_block_2
import Theorems.Thm_MazurTransfer_order49_division_eval_block_3
import Theorems.Thm_MazurTransfer_order49_division_eval_block_4
open Polynomial
theorem MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock0 (d : ℚ) (i : Fin 5) :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.DivisionEvalCertificate d ((i : ℚ) + 0) := by
  exact MazurTransfer.order49_division_eval_block_0 d i

theorem MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock1 (d : ℚ) (i : Fin 5) :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.DivisionEvalCertificate d ((i : ℚ) + 5) := by
  exact MazurTransfer.order49_division_eval_block_1 d i

theorem MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock2 (d : ℚ) (i : Fin 5) :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.DivisionEvalCertificate d ((i : ℚ) + 10) := by
  exact MazurTransfer.order49_division_eval_block_2 d i

theorem MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock3 (d : ℚ) (i : Fin 5) :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.DivisionEvalCertificate d ((i : ℚ) + 15) := by
  exact MazurTransfer.order49_division_eval_block_3 d i

theorem MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock4 (d : ℚ) (i : Fin 5) :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.DivisionEvalCertificate d ((i : ℚ) + 20) := by
  exact MazurTransfer.order49_division_eval_block_4 d i
namespace MazurTransfer.Order49ArithmeticAggregateConsumers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

noncomputable section

namespace Internal

-- In the coefficient declarations below, `X : ℚ[X]` is the parameter `D`.




























































































































































































































































































































































































































































































































































































































end Internal

















namespace Internal





end Internal









lemma divisionCofactorData0_degree :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData0.natDegree ≤ 7 := by
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData0
  compute_degree

lemma divisionCofactorData1_degree :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData1.natDegree ≤ 7 := by
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData1
  compute_degree

lemma divisionCofactorData2_degree :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData2.natDegree ≤ 7 := by
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData2
  compute_degree

lemma divisionCofactor0_degree (d : ℚ) :
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d).natDegree ≤ 7 := by
  exact natDegree_map_le.trans MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData0_degree

lemma divisionCofactor1_degree (d : ℚ) :
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d).natDegree ≤ 7 := by
  exact natDegree_map_le.trans MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData1_degree

lemma divisionCofactor2_degree (d : ℚ) :
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2 d).natDegree ≤ 7 := by
  exact natDegree_map_le.trans MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData2_degree





































namespace Internal






















































end Internal

end

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end
end MazurTransfer.Order49ArithmeticAggregateConsumers

namespace MazurTransfer.Order49ArithmeticAggregateConsumers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate



private lemma dualKernelPolynomial_degree (d : ℚ) :
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.dualKernelPolynomial d).natDegree ≤ 3 := by
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.dualKernelPolynomial
  compute_degree







private theorem division_eval_fin (d : ℚ) (i : Fin 25) :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.DivisionEvalCertificate d (i : ℚ) := by
  fin_cases i
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock0 d (0 : Fin 5) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock0 d (1 : Fin 5) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock0 d (2 : Fin 5) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock0 d (3 : Fin 5) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock0 d (4 : Fin 5) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock1 d (0 : Fin 5) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock1 d (1 : Fin 5) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock1 d (2 : Fin 5) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock1 d (3 : Fin 5) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock1 d (4 : Fin 5) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock2 d (0 : Fin 5) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock2 d (1 : Fin 5) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock2 d (2 : Fin 5) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock2 d (3 : Fin 5) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock2 d (4 : Fin 5) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock3 d (0 : Fin 5) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock3 d (1 : Fin 5) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock3 d (2 : Fin 5) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock3 d (3 : Fin 5) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock3 d (4 : Fin 5) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock4 d (0 : Fin 5) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock4 d (1 : Fin 5) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock4 d (2 : Fin 5) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock4 d (3 : Fin 5) using 1; norm_num)
  · (convert MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock4 d (4 : Fin 5) using 1; norm_num)

private lemma quotient_prePsi_seven_degree (d : ℚ) :
    ((MazurTorsion.Kubert.orderSevenQuotient d).preΨ' 7).natDegree ≤ 24 := by
  apply le_trans ((MazurTorsion.Kubert.orderSevenQuotient d).natDegree_preΨ'_le 7)
  have hodd : ¬Even (7 : ℕ) := by decide
  simp [hodd]

private lemma division_factor_product_degree (d : ℚ) :
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.dualKernelPolynomial d * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d *
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2 d).natDegree ≤ 24 := by
  have h0 : (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.dualKernelPolynomial d *
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d).natDegree ≤ 10 :=
    le_trans natDegree_mul_le
      (Nat.add_le_add (MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.dualKernelPolynomial_degree d)
        (MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0_degree d))
  have h1 : (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.dualKernelPolynomial d * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d *
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d).natDegree ≤ 17 :=
    le_trans natDegree_mul_le
      (Nat.add_le_add h0 (MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1_degree d))
  exact le_trans natDegree_mul_le
    (Nat.add_le_add h1 (MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2_degree d))

private theorem quotient_prePsi_seven_polynomial_factorization (d : ℚ) :
    (MazurTorsion.Kubert.orderSevenQuotient d).preΨ' 7 =
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.dualKernelPolynomial d * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d *
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2 d := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    _ _ (f := fun i : Fin 25 ↦ (i : ℚ))
  · intro i j hij
    apply Fin.ext
    exact Nat.cast_injective hij
  · intro i
    exact MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.division_eval_fin d i
  · simp only [Fintype.card_fin]
    have hl := MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.quotient_prePsi_seven_degree d
    have hr := MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.division_factor_product_degree d
    omega



end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end MazurTransfer.Order49ArithmeticAggregateConsumers

theorem solution (d : ℚ) :
    (MazurTorsion.Kubert.orderSevenQuotient d).preΨ' 7 =
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.dualKernelPolynomial d * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d *
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2 d := by
  exact MazurTransfer.Order49ArithmeticAggregateConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.quotient_prePsi_seven_polynomial_factorization d
#print axioms solution
