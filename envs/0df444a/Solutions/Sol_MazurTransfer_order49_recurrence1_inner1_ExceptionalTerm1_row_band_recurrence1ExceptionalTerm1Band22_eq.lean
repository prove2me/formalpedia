-- Prove2me | solution 1 for MazurTransfer.order49_recurrence1_inner1_ExceptionalTerm1_row_band_recurrence1ExceptionalTerm1Band22_eq
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T09:52:10.13239+00:00
-- url     : https://prove2.me/submissions/45fda8e3-2772-49d9-95b6-931b2786c066

import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm1ExactRowBandDataPart5
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm1ExactRowBandDataPart6
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm1ExactRowBandDataPart7
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm1ExactRowBandDataPart8
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner1ExactHelperDataPart3
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial
open _root_.MazurTorsion
open _root_.MazurTorsion.Kubert
namespace RB1ExceptionalTerm1
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section











































theorem recurrence1ExceptionalTerm1Band22_eq :
    MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Band22 = MazurTransfer.Order49Recurrence1Inner1ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Block22 := by
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Band22 MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row5Band22
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row6Band22 MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Row7Band22
  unfold MazurTransfer.Order49Recurrence1Inner1ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Block22
  ring





end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end RB1ExceptionalTerm1

theorem solution :
    MazurTransfer.Order49Recurrence1ExceptionalTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Band22 = MazurTransfer.Order49Recurrence1Inner1ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Block22 := by
  exact RB1ExceptionalTerm1.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1Band22_eq
#print axioms solution
