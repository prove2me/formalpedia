-- Prove2me | solution 1 for MazurTransfer.order49_division_eval_block_3
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T03:17:11.605421+00:00
-- url     : https://prove2.me/submissions/4c7de346-02ac-4531-9fad-9770e5e4e79c

import Definitions.Def_MazurTransfer_Order49DirectEvaluationPredicates
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Theorems.Thm_MazurTransfer_order49_division_original_eval_15
import Theorems.Thm_MazurTransfer_order49_division_original_eval_16
import Theorems.Thm_MazurTransfer_order49_division_original_eval_17
import Theorems.Thm_MazurTransfer_order49_division_original_eval_18
import Theorems.Thm_MazurTransfer_order49_division_original_eval_19
open Polynomial
theorem MazurTransfer.Order49TimeoutBlockConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.eval_15 (d : ℚ) :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.DivisionEvalCertificate d 15 := by
  exact MazurTransfer.order49_division_original_eval_15 d

theorem MazurTransfer.Order49TimeoutBlockConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.eval_16 (d : ℚ) :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.DivisionEvalCertificate d 16 := by
  exact MazurTransfer.order49_division_original_eval_16 d

theorem MazurTransfer.Order49TimeoutBlockConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.eval_17 (d : ℚ) :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.DivisionEvalCertificate d 17 := by
  exact MazurTransfer.order49_division_original_eval_17 d

theorem MazurTransfer.Order49TimeoutBlockConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.eval_18 (d : ℚ) :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.DivisionEvalCertificate d 18 := by
  exact MazurTransfer.order49_division_original_eval_18 d

theorem MazurTransfer.Order49TimeoutBlockConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.eval_19 (d : ℚ) :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.DivisionEvalCertificate d 19 := by
  exact MazurTransfer.order49_division_original_eval_19 d
namespace MazurTransfer.Order49TimeoutBlockConsumers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/




namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal











theorem divisionEvalBlock3 (d : ℚ) (i : Fin 5) :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.DivisionEvalCertificate d ((i : ℚ) + 15) := by
  fin_cases i
  · (convert MazurTransfer.Order49TimeoutBlockConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.eval_15 d using 1; norm_num)
  · (convert MazurTransfer.Order49TimeoutBlockConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.eval_16 d using 1; norm_num)
  · (convert MazurTransfer.Order49TimeoutBlockConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.eval_17 d using 1; norm_num)
  · (convert MazurTransfer.Order49TimeoutBlockConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.eval_18 d using 1; norm_num)
  · (convert MazurTransfer.Order49TimeoutBlockConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.eval_19 d using 1; norm_num)

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end MazurTransfer.Order49TimeoutBlockConsumers

theorem solution (d : ℚ) (i : Fin 5) :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.DivisionEvalCertificate d ((i : ℚ) + 15) := by
  exact MazurTransfer.Order49TimeoutBlockConsumers.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionEvalBlock3 d i
#print axioms solution
