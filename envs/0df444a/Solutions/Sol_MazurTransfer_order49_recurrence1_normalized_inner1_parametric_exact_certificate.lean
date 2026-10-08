-- Prove2me | solution 1 for MazurTransfer.order49_recurrence1_normalized_inner1_parametric_exact_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T09:36:49.538643+00:00
-- url     : https://prove2.me/submissions/5cef8411-01b8-4948-92c5-8be7125c2e8d

import Definitions.Def_MazurTransfer_ExactEqualityCertificate
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner1ExactHelperDataPart0
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner1ExactHelperDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner1ExactHelperDataPart2
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner1ExactHelperDataPart3
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner5ExactHelperData
import Definitions.Def_MazurTransfer_Order49Recurrence1NormalizedData
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
import Theorems.Thm_MazurTransfer_order49_recurrence1_inner1_exact_helper_ExceptionalTerm1_eq
import Theorems.Thm_MazurTransfer_order49_recurrence1_inner1_exact_helper_Left1_eq
import Theorems.Thm_MazurTransfer_order49_recurrence1_inner1_exact_helper_QuotientTerm1_eq
import Theorems.Thm_MazurTransfer_order49_recurrence1_inner1_exact_helper_Residual1
import Theorems.Thm_MazurTransfer_order49_recurrence1_inner1_exact_helper_ShiftTerm1_eq
import Theorems.Thm_MazurTransfer_order49_recurrence1_inner5_helper_recurrence1B6Square_eq
open Polynomial
theorem Normalized1.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1_eq :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Exceptional * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder31 =
      MazurTransfer.Order49Recurrence1Inner1ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1 := by
  exact MazurTransfer.order49_recurrence1_inner1_exact_helper_ExceptionalTerm1_eq.identity

theorem Normalized1.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left1_eq :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source1 * MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6Square =
      MazurTransfer.Order49Recurrence1Inner1ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left1 := by
  exact MazurTransfer.order49_recurrence1_inner1_exact_helper_Left1_eq.identity

theorem Normalized1.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1_eq :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientConstant * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder21 =
      MazurTransfer.Order49Recurrence1Inner1ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1 := by
  exact MazurTransfer.order49_recurrence1_inner1_exact_helper_QuotientTerm1_eq.identity

theorem Normalized1.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Residual1 :
    MazurTransfer.Order49Recurrence1Inner1ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left1 =
      MazurTransfer.Order49Recurrence1Inner1ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1 +
      MazurTransfer.Order49Recurrence1Inner1ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1 +
      MazurTransfer.Order49Recurrence1Inner1ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1 := by
  exact MazurTransfer.order49_recurrence1_inner1_exact_helper_Residual1

theorem Normalized1.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1_eq :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder20 =
      MazurTransfer.Order49Recurrence1Inner1ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1 := by
  exact MazurTransfer.order49_recurrence1_inner1_exact_helper_ShiftTerm1_eq.identity

theorem Normalized1.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6Square_eq :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26 =
      MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6Square := by
  exact MazurTransfer.order49_recurrence1_inner5_helper_recurrence1B6Square_eq

namespace Normalized1
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence1NormalizedInner1 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26 ^ 2 *
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source1 =
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder20 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26 +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder21 *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientConstant +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Exceptional *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder31 := by
  calc
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26 ^ 2 *
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source1 =
      MazurTransfer.Order49Recurrence1Inner1ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left1 := by
        rw [pow_two, Normalized1.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6Square_eq]
        rw [mul_comm, Normalized1.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left1_eq]
    _ =
        MazurTransfer.Order49Recurrence1Inner1ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1 +
        MazurTransfer.Order49Recurrence1Inner1ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1 +
        MazurTransfer.Order49Recurrence1Inner1ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1 := Normalized1.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Residual1
    _ = _ := by
      rw [← Normalized1.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1_eq]
      rw [← Normalized1.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1_eq]
      rw [← Normalized1.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1_eq]
      ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end Normalized1

theorem solution : MazurTransfer.ExactEqualityCertificate (α := Polynomial ℚ)
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26 ^ 2 *
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source1)
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder20 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26 +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder21 *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientConstant +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Exceptional *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder31) := by
  exact ⟨Normalized1.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1NormalizedInner1⟩
#print axioms solution
