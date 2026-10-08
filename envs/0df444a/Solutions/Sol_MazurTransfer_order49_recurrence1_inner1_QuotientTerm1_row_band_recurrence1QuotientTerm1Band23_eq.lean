-- Prove2me | solution 1 for MazurTransfer.order49_recurrence1_inner1_QuotientTerm1_row_band_recurrence1QuotientTerm1Band23_eq
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T09:52:12.203077+00:00
-- url     : https://prove2.me/submissions/117acc95-d5d6-4c55-be80-c6368c5720f2

import Definitions.Def_MazurTransfer_Order49Recurrence1Inner1ExactHelperDataPart2
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm1ExactRowBandDataPart10
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm1ExactRowBandDataPart11
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















































theorem recurrence1QuotientTerm1Band23_eq :
    MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Band23 = MazurTransfer.Order49Recurrence1Inner1ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Block23 := by
  unfold MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Band23 MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Row10Band23
  unfold MazurTransfer.Order49Recurrence1Inner1ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Block23
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end RB1QuotientTerm1

theorem solution :
    MazurTransfer.Order49Recurrence1QuotientTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Band23 = MazurTransfer.Order49Recurrence1Inner1ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Block23 := by
  exact RB1QuotientTerm1.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1Band23_eq
#print axioms solution
