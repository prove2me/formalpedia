-- Prove2me | solution 1 for MazurTransfer.order49_recurrence1_inner_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T02:46:14.667687+00:00
-- url     : https://prove2.me/submissions/a3c7c918-6f78-45cf-8166-fbce383bb6bb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MazurTransfer_Order49BacktrackingCofactors
import Definitions.Def_MazurTransfer_Order49Recurrence1NormalizedData
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData1
import Mathlib
import Theorems.Thm_MazurTransfer_order49_recurrence1_divisionCofactor0Coefficient1_eq_normalized
import Theorems.Thm_MazurTransfer_order49_recurrence1_divisionCofactor0Coefficient6_eq_normalized
import Theorems.Thm_MazurTransfer_order49_recurrence1_divisionCofactor0Coefficient7_eq_normalized
import Theorems.Thm_MazurTransfer_order49_recurrence1_exceptional1_eq_normalized
import Theorems.Thm_MazurTransfer_order49_recurrence1_recurrence1NormalizedInner1
import Theorems.Thm_MazurTransfer_order49_recurrence1_recurrence1QuotientConstant_eq
import Theorems.Thm_MazurTransfer_order49_recurrence1_remainder2Coefficient0_eq_normalized
import Theorems.Thm_MazurTransfer_order49_recurrence1_remainder2Coefficient1_eq_normalized
import Theorems.Thm_MazurTransfer_order49_recurrence1_remainder2Coefficient5_eq_normalized
import Theorems.Thm_MazurTransfer_order49_recurrence1_remainder2Coefficient6_eq_normalized
import Theorems.Thm_MazurTransfer_order49_recurrence1_remainder3Coefficient1_eq_normalized
open Polynomial
theorem MazurTransfer.Order49Recurrence1DirectStandalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.divisionCofactor0Coefficient1_eq_normalized :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient1 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source1 := by
  exact MazurTransfer.order49_recurrence1_divisionCofactor0Coefficient1_eq_normalized
theorem MazurTransfer.Order49Recurrence1DirectStandalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.divisionCofactor0Coefficient6_eq_normalized :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient6 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source6 := by
  exact MazurTransfer.order49_recurrence1_divisionCofactor0Coefficient6_eq_normalized
theorem MazurTransfer.Order49Recurrence1DirectStandalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.divisionCofactor0Coefficient7_eq_normalized :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source7 := by
  exact MazurTransfer.order49_recurrence1_divisionCofactor0Coefficient7_eq_normalized
theorem MazurTransfer.Order49Recurrence1DirectStandalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional1_eq_normalized :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional1 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Exceptional := by
  exact MazurTransfer.order49_recurrence1_exceptional1_eq_normalized
theorem MazurTransfer.Order49Recurrence1DirectStandalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1NormalizedInner1 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26 ^ 2 *
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source1 =
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder20 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26 +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder21 *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientConstant +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Exceptional *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder31 := by
  exact MazurTransfer.order49_recurrence1_recurrence1NormalizedInner1
theorem MazurTransfer.Order49Recurrence1DirectStandalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientConstant_eq :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source6 -
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source7 =
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientConstant := by
  exact MazurTransfer.order49_recurrence1_recurrence1QuotientConstant_eq
theorem MazurTransfer.Order49Recurrence1DirectStandalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient0_eq_normalized :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient0 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder20 := by
  exact MazurTransfer.order49_recurrence1_remainder2Coefficient0_eq_normalized
theorem MazurTransfer.Order49Recurrence1DirectStandalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient1_eq_normalized :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient1 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder21 := by
  exact MazurTransfer.order49_recurrence1_remainder2Coefficient1_eq_normalized
theorem MazurTransfer.Order49Recurrence1DirectStandalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5_eq_normalized :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25 := by
  exact MazurTransfer.order49_recurrence1_remainder2Coefficient5_eq_normalized
theorem MazurTransfer.Order49Recurrence1DirectStandalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6_eq_normalized :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26 := by
  exact MazurTransfer.order49_recurrence1_remainder2Coefficient6_eq_normalized
theorem MazurTransfer.Order49Recurrence1DirectStandalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient1_eq_normalized :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient1 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder31 := by
  exact MazurTransfer.order49_recurrence1_remainder3Coefficient1_eq_normalized
namespace MazurTransfer.Order49Recurrence1DirectStandalone
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence1_inner_1 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 ^ 2 *
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient1 =
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient0 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 *
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7) +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient1 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 *
              MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient6 -
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5 *
              MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7) +
        (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7 ^ 2 *
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional1) *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient1 := by
  rw [MazurTransfer.Order49Recurrence1DirectStandalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.divisionCofactor0Coefficient1_eq_normalized]
  rw [MazurTransfer.Order49Recurrence1DirectStandalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.divisionCofactor0Coefficient6_eq_normalized]
  rw [MazurTransfer.Order49Recurrence1DirectStandalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.divisionCofactor0Coefficient7_eq_normalized]
  rw [MazurTransfer.Order49Recurrence1DirectStandalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient1_eq_normalized]
  rw [MazurTransfer.Order49Recurrence1DirectStandalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5_eq_normalized]
  rw [MazurTransfer.Order49Recurrence1DirectStandalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6_eq_normalized]
  rw [MazurTransfer.Order49Recurrence1DirectStandalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient1_eq_normalized]
  rw [MazurTransfer.Order49Recurrence1DirectStandalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional1_eq_normalized]
  rw [MazurTransfer.Order49Recurrence1DirectStandalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient0_eq_normalized]
  rw [MazurTransfer.Order49Recurrence1DirectStandalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientConstant_eq]
  simpa [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source7, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source7Block0]
    using MazurTransfer.Order49Recurrence1DirectStandalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1NormalizedInner1









end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end MazurTransfer.Order49Recurrence1DirectStandalone

theorem solution :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 ^ 2 *
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient1 =
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient0 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 *
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7) +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient1 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 *
              MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient6 -
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5 *
              MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7) +
        (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7 ^ 2 *
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional1) *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient1 := by
  exact MazurTransfer.Order49Recurrence1DirectStandalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1_inner_1
#print axioms solution
