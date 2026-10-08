-- Prove2me | solution 1 for MazurTransfer.order49_recurrence1_inner3_ExceptionalTerm3_row_band_recurrence1ExceptionalTerm3Band16_eq
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T10:18:51.861549+00:00
-- url     : https://prove2.me/submissions/1ba5628a-1aa2-4a2e-a73b-1238ff609a8d

import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm3ExactRowBandDataPart0
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm3ExactRowBandDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm3ExactRowBandDataPart2
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm3ExactRowBandDataPart3
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm3ExactRowBandDataPart4
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm3ExactRowBandDataPart5
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm3ExactRowBandDataPart6
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm3ExactRowBandDataPart7
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm3ExactRowBandDataPart8
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner3ExactHelperDataPart3
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial
open _root_.MazurTorsion
open _root_.MazurTorsion.Kubert
namespace RB3ExceptionalTerm3
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

















































































































































































































































































































































































private theorem recurrence1ExceptionalTerm3Band16_eq :
    MazurTransfer.Order49Recurrence1ExceptionalTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Band16 = MazurTransfer.Order49Recurrence1Inner3ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Block16 := by
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Band16 MazurTransfer.Order49Recurrence1ExceptionalTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Row0Band16
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Row1Band16 MazurTransfer.Order49Recurrence1ExceptionalTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Row2Band16
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Row3Band16 MazurTransfer.Order49Recurrence1ExceptionalTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Row4Band16
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Row5Band16 MazurTransfer.Order49Recurrence1ExceptionalTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Row6Band16
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Row7Band16 MazurTransfer.Order49Recurrence1Inner3ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Block16
  ring































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end RB3ExceptionalTerm3

theorem solution :
    MazurTransfer.Order49Recurrence1ExceptionalTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Band16 = MazurTransfer.Order49Recurrence1Inner3ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Block16 := by
  exact RB3ExceptionalTerm3.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Band16_eq
#print axioms solution
