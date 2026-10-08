-- Prove2me | solution 1 for MazurTransfer.order49_recurrence1_inner3_QuotientTerm3_row_band_recurrence1QuotientTerm3Band11_eq
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T11:00:29.255015+00:00
-- url     : https://prove2.me/submissions/8c2a4a98-d28a-4dfd-9f51-da6d1d5ba636

import Definitions.Def_MazurTransfer_Order49Recurrence1Inner3ExactHelperDataPart2
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm3ExactRowBandDataPart0
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm3ExactRowBandDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm3ExactRowBandDataPart10
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm3ExactRowBandDataPart11
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm3ExactRowBandDataPart2
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm3ExactRowBandDataPart3
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm3ExactRowBandDataPart4
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm3ExactRowBandDataPart5
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm3ExactRowBandDataPart6
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm3ExactRowBandDataPart7
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm3ExactRowBandDataPart8
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm3ExactRowBandDataPart9
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial
open _root_.MazurTorsion
open _root_.MazurTorsion.Kubert
namespace RB3QuotientTerm3
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

























































































































































































































































































































































































private theorem recurrence1QuotientTerm3Band11_eq :
    MazurTransfer.Order49Recurrence1QuotientTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Band11 = MazurTransfer.Order49Recurrence1Inner3ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Block11 := by
  unfold MazurTransfer.Order49Recurrence1QuotientTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Band11 MazurTransfer.Order49Recurrence1QuotientTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Row0Band11
  unfold MazurTransfer.Order49Recurrence1QuotientTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Row1Band11 MazurTransfer.Order49Recurrence1QuotientTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Row2Band11
  unfold MazurTransfer.Order49Recurrence1QuotientTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Row3Band11 MazurTransfer.Order49Recurrence1QuotientTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Row4Band11
  unfold MazurTransfer.Order49Recurrence1QuotientTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Row5Band11 MazurTransfer.Order49Recurrence1QuotientTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Row6Band11
  unfold MazurTransfer.Order49Recurrence1QuotientTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Row7Band11 MazurTransfer.Order49Recurrence1QuotientTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Row8Band11
  unfold MazurTransfer.Order49Recurrence1QuotientTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Row9Band11 MazurTransfer.Order49Recurrence1QuotientTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Row10Band11
  unfold MazurTransfer.Order49Recurrence1Inner3ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Block11
  ring



















































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end RB3QuotientTerm3

theorem solution :
    MazurTransfer.Order49Recurrence1QuotientTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Band11 = MazurTransfer.Order49Recurrence1Inner3ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Block11 := by
  exact RB3QuotientTerm3.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Band11_eq
#print axioms solution
