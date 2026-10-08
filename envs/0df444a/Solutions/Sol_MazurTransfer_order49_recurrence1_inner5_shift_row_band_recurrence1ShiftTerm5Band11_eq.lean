-- Prove2me | solution 1 for MazurTransfer.order49_recurrence1_inner5_shift_row_band_recurrence1ShiftTerm5Band11_eq
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T08:43:17.891038+00:00
-- url     : https://prove2.me/submissions/acb27657-c178-4172-8846-b809df0b6d4b

import Definitions.Def_MazurTransfer_Order49Recurrence1Inner5ExactHelperData
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftExactRowBandDataPart0
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftExactRowBandDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftExactRowBandDataPart10
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftExactRowBandDataPart11
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftExactRowBandDataPart2
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftExactRowBandDataPart3
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftExactRowBandDataPart4
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftExactRowBandDataPart5
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftExactRowBandDataPart6
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftExactRowBandDataPart7
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftExactRowBandDataPart8
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftExactRowBandDataPart9
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial
open _root_.MazurTorsion
open _root_.MazurTorsion.Kubert
namespace H5
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section























































































































































































































































































































































































private theorem recurrence1ShiftTerm5Band11_eq :
    MazurTransfer.Order49Recurrence1ShiftExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm5Band11 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm5Block11 := by
  unfold MazurTransfer.Order49Recurrence1ShiftExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm5Band11 MazurTransfer.Order49Recurrence1ShiftExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm5Row0Band11 MazurTransfer.Order49Recurrence1ShiftExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm5Row1Band11
  unfold MazurTransfer.Order49Recurrence1ShiftExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm5Row2Band11 MazurTransfer.Order49Recurrence1ShiftExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm5Row3Band11
  unfold MazurTransfer.Order49Recurrence1ShiftExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm5Row4Band11 MazurTransfer.Order49Recurrence1ShiftExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm5Row5Band11
  unfold MazurTransfer.Order49Recurrence1ShiftExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm5Row6Band11 MazurTransfer.Order49Recurrence1ShiftExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm5Row7Band11
  unfold MazurTransfer.Order49Recurrence1ShiftExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm5Row8Band11 MazurTransfer.Order49Recurrence1ShiftExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm5Row9Band11
  unfold MazurTransfer.Order49Recurrence1ShiftExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm5Row10Band11 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm5Block11
  ring















































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end H5

theorem solution :
    MazurTransfer.Order49Recurrence1ShiftExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm5Band11 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm5Block11 := by
  exact H5.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm5Band11_eq
#print axioms solution
