-- Prove2me | solution 1 for MazurTransfer.order49_doubling_eval_block_6
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T03:15:19.936113+00:00
-- url     : https://prove2.me/submissions/0e30bd1c-facc-43ea-9d65-ac7301120f8c

import Definitions.Def_MazurTransfer_Order49DirectEvaluationPredicates
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Theorems.Thm_MazurTransfer_order49_doubling_original_eval_24
import Theorems.Thm_MazurTransfer_order49_doubling_original_eval_25
import Theorems.Thm_MazurTransfer_order49_doubling_original_eval_26
import Theorems.Thm_MazurTransfer_order49_doubling_original_eval_27
open Polynomial
theorem MazurTransfer.Order49TimeoutBlockConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.eval_24 (d : ℚ) : MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.EvalCertificate d 24 := by
  exact MazurTransfer.order49_doubling_original_eval_24 d

theorem MazurTransfer.Order49TimeoutBlockConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.eval_25 (d : ℚ) : MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.EvalCertificate d 25 := by
  exact MazurTransfer.order49_doubling_original_eval_25 d

theorem MazurTransfer.Order49TimeoutBlockConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.eval_26 (d : ℚ) : MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.EvalCertificate d 26 := by
  exact MazurTransfer.order49_doubling_original_eval_26 d

theorem MazurTransfer.Order49TimeoutBlockConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.eval_27 (d : ℚ) : MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.EvalCertificate d 27 := by
  exact MazurTransfer.order49_doubling_original_eval_27 d
namespace MazurTransfer.Order49TimeoutBlockConsumers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



namespace MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal











theorem evalBlock6 (d : ℚ) (i : Fin 4) :
    MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.EvalCertificate d ((i : ℚ) + 24) := by
  fin_cases i
  · (convert MazurTransfer.Order49TimeoutBlockConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.eval_24 d using 1; norm_num)
  · (convert MazurTransfer.Order49TimeoutBlockConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.eval_25 d using 1; norm_num)
  · (convert MazurTransfer.Order49TimeoutBlockConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.eval_26 d using 1; norm_num)
  · (convert MazurTransfer.Order49TimeoutBlockConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.eval_27 d using 1; norm_num)

end MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal

end MazurTransfer.Order49TimeoutBlockConsumers

theorem solution (d : ℚ) (i : Fin 4) :
    MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.EvalCertificate d ((i : ℚ) + 24) := by
  exact MazurTransfer.Order49TimeoutBlockConsumers.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock6 d i
#print axioms solution
