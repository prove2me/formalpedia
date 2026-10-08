-- Prove2me | solution 1 for MazurTransfer.order49_recurrence1_inner4_QuotientTerm4_row_band_recurrence1QuotientTerm4Band14_eq
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T10:20:44.952853+00:00
-- url     : https://prove2.me/submissions/a3c37461-c101-4a09-ae58-796840740ca3

import Definitions.Def_MazurTransfer_Order49Recurrence1Inner4ExactHelperDataPart2
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm4ExactRowBandDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm4ExactRowBandDataPart10
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm4ExactRowBandDataPart11
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm4ExactRowBandDataPart2
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm4ExactRowBandDataPart3
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm4ExactRowBandDataPart4
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm4ExactRowBandDataPart5
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm4ExactRowBandDataPart6
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm4ExactRowBandDataPart7
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm4ExactRowBandDataPart8
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm4ExactRowBandDataPart9
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial
open _root_.MazurTorsion
open _root_.MazurTorsion.Kubert
namespace RB4QuotientTerm4
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section





































































































































































































































































































































































































private theorem recurrence1QuotientTerm4Band14_eq :
    MazurTransfer.Order49Recurrence1QuotientTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm4Band14 = MazurTransfer.Order49Recurrence1Inner4ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm4Block14 := by
  unfold MazurTransfer.Order49Recurrence1QuotientTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm4Band14 MazurTransfer.Order49Recurrence1QuotientTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm4Row2Band14
  unfold MazurTransfer.Order49Recurrence1QuotientTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm4Row3Band14 MazurTransfer.Order49Recurrence1QuotientTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm4Row4Band14
  unfold MazurTransfer.Order49Recurrence1QuotientTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm4Row5Band14 MazurTransfer.Order49Recurrence1QuotientTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm4Row6Band14
  unfold MazurTransfer.Order49Recurrence1QuotientTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm4Row7Band14 MazurTransfer.Order49Recurrence1QuotientTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm4Row8Band14
  unfold MazurTransfer.Order49Recurrence1QuotientTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm4Row9Band14 MazurTransfer.Order49Recurrence1QuotientTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm4Row10Band14
  unfold MazurTransfer.Order49Recurrence1Inner4ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm4Block14
  ring







































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end RB4QuotientTerm4

theorem solution :
    MazurTransfer.Order49Recurrence1QuotientTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm4Band14 = MazurTransfer.Order49Recurrence1Inner4ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm4Block14 := by
  exact RB4QuotientTerm4.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm4Band14_eq
#print axioms solution
