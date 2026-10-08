-- Prove2me | solution 1 for MazurTransfer.order49_recurrence1_inner3_ExceptionalTerm3_row_band_recurrence1ExceptionalTerm3Band7_eq
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T10:19:52.812+00:00
-- url     : https://prove2.me/submissions/78cc6fe8-d213-4285-87a3-ecc51de30e27

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













































































































































































































































































































































private theorem recurrence1ExceptionalTerm3Band7_eq :
    MazurTransfer.Order49Recurrence1ExceptionalTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Band7 = MazurTransfer.Order49Recurrence1Inner3ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Block7 := by
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Band7 MazurTransfer.Order49Recurrence1ExceptionalTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Row0Band7
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Row1Band7 MazurTransfer.Order49Recurrence1ExceptionalTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Row2Band7
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Row3Band7 MazurTransfer.Order49Recurrence1ExceptionalTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Row4Band7
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Row5Band7 MazurTransfer.Order49Recurrence1ExceptionalTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Row6Band7
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Row7Band7 MazurTransfer.Order49Recurrence1Inner3ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Block7
  ring



































































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end RB3ExceptionalTerm3

theorem solution :
    MazurTransfer.Order49Recurrence1ExceptionalTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Band7 = MazurTransfer.Order49Recurrence1Inner3ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Block7 := by
  exact RB3ExceptionalTerm3.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm3Band7_eq
#print axioms solution
