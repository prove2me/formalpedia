-- Prove2me | solution 1 for MazurTransfer.order49_recurrence1_normalized_inner4_parametric_exact_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T09:40:31.20384+00:00
-- url     : https://prove2.me/submissions/fee66415-d0d5-4825-b688-d6071ff1df52

import Definitions.Def_MazurTransfer_ExactEqualityCertificate
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner4ExactHelperDataPart0
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner4ExactHelperDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner4ExactHelperDataPart2
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner4ExactHelperDataPart3
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner5ExactHelperData
import Definitions.Def_MazurTransfer_Order49Recurrence1NormalizedData
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
import Theorems.Thm_MazurTransfer_order49_recurrence1_inner4_exact_helper_ExceptionalTerm4_eq
import Theorems.Thm_MazurTransfer_order49_recurrence1_inner4_exact_helper_Left4_eq
import Theorems.Thm_MazurTransfer_order49_recurrence1_inner4_exact_helper_QuotientTerm4_eq
import Theorems.Thm_MazurTransfer_order49_recurrence1_inner4_exact_helper_Residual4
import Theorems.Thm_MazurTransfer_order49_recurrence1_inner4_exact_helper_ShiftTerm4_eq
import Theorems.Thm_MazurTransfer_order49_recurrence1_inner5_helper_recurrence1B6Square_eq
open Polynomial
theorem Normalized4.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4_eq :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Exceptional * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34 =
      MazurTransfer.Order49Recurrence1Inner4ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4 := by
  exact MazurTransfer.order49_recurrence1_inner4_exact_helper_ExceptionalTerm4_eq.identity

theorem Normalized4.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left4_eq :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source4 * MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6Square =
      MazurTransfer.Order49Recurrence1Inner4ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left4 := by
  exact MazurTransfer.order49_recurrence1_inner4_exact_helper_Left4_eq.identity

theorem Normalized4.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm4_eq :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientConstant * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder24 =
      MazurTransfer.Order49Recurrence1Inner4ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm4 := by
  exact MazurTransfer.order49_recurrence1_inner4_exact_helper_QuotientTerm4_eq.identity

theorem Normalized4.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Residual4 :
    MazurTransfer.Order49Recurrence1Inner4ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left4 =
      MazurTransfer.Order49Recurrence1Inner4ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4 +
      MazurTransfer.Order49Recurrence1Inner4ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm4 +
      MazurTransfer.Order49Recurrence1Inner4ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4 := by
  exact MazurTransfer.order49_recurrence1_inner4_exact_helper_Residual4

theorem Normalized4.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4_eq :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder23 =
      MazurTransfer.Order49Recurrence1Inner4ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4 := by
  exact MazurTransfer.order49_recurrence1_inner4_exact_helper_ShiftTerm4_eq.identity

theorem Normalized4.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6Square_eq :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26 =
      MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6Square := by
  exact MazurTransfer.order49_recurrence1_inner5_helper_recurrence1B6Square_eq

namespace Normalized4
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence1NormalizedInner4 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26 ^ 2 *
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source4 =
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder23 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26 +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder24 *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientConstant +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Exceptional *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34 := by
  calc
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26 ^ 2 *
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source4 =
      MazurTransfer.Order49Recurrence1Inner4ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left4 := by
        rw [pow_two, Normalized4.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6Square_eq]
        rw [mul_comm, Normalized4.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left4_eq]
    _ =
        MazurTransfer.Order49Recurrence1Inner4ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4 +
        MazurTransfer.Order49Recurrence1Inner4ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm4 +
        MazurTransfer.Order49Recurrence1Inner4ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4 := Normalized4.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Residual4
    _ = _ := by
      rw [← Normalized4.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4_eq]
      rw [← Normalized4.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm4_eq]
      rw [← Normalized4.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4_eq]
      ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end Normalized4

theorem solution : MazurTransfer.ExactEqualityCertificate (α := Polynomial ℚ)
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26 ^ 2 *
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source4)
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder23 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26 +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder24 *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientConstant +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Exceptional *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34) := by
  exact ⟨Normalized4.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1NormalizedInner4⟩
#print axioms solution
