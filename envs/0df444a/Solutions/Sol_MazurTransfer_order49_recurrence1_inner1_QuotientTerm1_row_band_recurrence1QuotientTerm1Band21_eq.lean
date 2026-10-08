-- Prove2me | solution 1 for MazurTransfer.order49_recurrence1_inner1_QuotientTerm1_row_band_recurrence1QuotientTerm1Band21_eq
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T09:52:01.567894+00:00
-- url     : https://prove2.me/submissions/0e204af5-f1fa-4706-b6df-6502f556b0d1

import Definitions.Def_MazurTransfer_Order49Recurrence1Inner1ExactHelperDataPart2
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm1ExactRowBandDataPart10
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm1ExactRowBandDataPart11
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm1ExactRowBandDataPart8
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm1ExactRowBandDataPart9
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial
open _root_.MazurTorsion
open _root_.MazurTorsion.Kubert
namespace RB1QuotientTerm1
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section







































theorem recurrence1QuotientTerm1Band21_eq :
    MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Band21 = MazurTransfer.Order49Recurrence1Inner1ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Block21 := by
  unfold MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Band21 MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row8Band21
  unfold MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row9Band21 MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row10Band21
  unfold MazurTransfer.Order49Recurrence1Inner1ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Block21
  ring









end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end RB1QuotientTerm1

theorem solution :
    MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Band21 = MazurTransfer.Order49Recurrence1Inner1ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Block21 := by
  exact RB1QuotientTerm1.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Band21_eq
#print axioms solution
