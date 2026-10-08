-- Prove2me | solution 1 for MazurTransfer.order49_recurrence1_inner3_QuotientTerm3_row_band_recurrence1QuotientTerm3Band9_eq
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T11:02:13.064926+00:00
-- url     : https://prove2.me/submissions/53ca6d78-e931-4f6d-be41-37e5c095e007

import Definitions.Def_MazurTransfer_Order49Recurrence1Inner3ExactHelperDataPart2
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm3ExactRowBandDataPart0
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm3ExactRowBandDataPart1
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

















































































































































































































































































































































































private theorem recurrence1QuotientTerm3Band9_eq :
    MazurTransfer.Order49Recurrence1QuotientTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Band9 = MazurTransfer.Order49Recurrence1Inner3ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Block9 := by
  unfold MazurTransfer.Order49Recurrence1QuotientTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Band9 MazurTransfer.Order49Recurrence1QuotientTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Row0Band9
  unfold MazurTransfer.Order49Recurrence1QuotientTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Row1Band9 MazurTransfer.Order49Recurrence1QuotientTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Row2Band9
  unfold MazurTransfer.Order49Recurrence1QuotientTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Row3Band9 MazurTransfer.Order49Recurrence1QuotientTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Row4Band9
  unfold MazurTransfer.Order49Recurrence1QuotientTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Row5Band9 MazurTransfer.Order49Recurrence1QuotientTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Row6Band9
  unfold MazurTransfer.Order49Recurrence1QuotientTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Row7Band9 MazurTransfer.Order49Recurrence1QuotientTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Row8Band9
  unfold MazurTransfer.Order49Recurrence1QuotientTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Row9Band9 MazurTransfer.Order49Recurrence1Inner3ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Block9
  ring



























































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end RB3QuotientTerm3

theorem solution :
    MazurTransfer.Order49Recurrence1QuotientTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Band9 = MazurTransfer.Order49Recurrence1Inner3ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Block9 := by
  exact RB3QuotientTerm3.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm3Band9_eq
#print axioms solution
