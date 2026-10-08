-- Prove2me | solution 1 for MazurTransfer.order49_recurrence1_inner4_ShiftTerm4_row_band_recurrence1ShiftTerm4Band13_eq
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T11:17:31.871647+00:00
-- url     : https://prove2.me/submissions/d092198a-8eda-41e2-bed7-15dd7c7e5a17

import Definitions.Def_MazurTransfer_Order49Recurrence1Inner4ExactHelperDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm4ExactRowBandDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm4ExactRowBandDataPart10
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm4ExactRowBandDataPart11
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm4ExactRowBandDataPart2
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm4ExactRowBandDataPart3
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm4ExactRowBandDataPart4
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm4ExactRowBandDataPart5
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm4ExactRowBandDataPart6
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm4ExactRowBandDataPart7
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm4ExactRowBandDataPart8
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm4ExactRowBandDataPart9
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial
open _root_.MazurTorsion
open _root_.MazurTorsion.Kubert
namespace RB4ShiftTerm4
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

































































































































































































































































































































































































private theorem recurrence1ShiftTerm4Band13_eq :
    MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Band13 = MazurTransfer.Order49Recurrence1Inner4ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Block13 := by
  unfold MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Band13 MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row1Band13 MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row2Band13
  unfold MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row3Band13 MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row4Band13
  unfold MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row5Band13 MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row6Band13
  unfold MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row7Band13 MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row8Band13
  unfold MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9Band13 MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row10Band13
  unfold MazurTransfer.Order49Recurrence1Inner4ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Block13
  ring











































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end RB4ShiftTerm4

theorem solution :
    MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Band13 = MazurTransfer.Order49Recurrence1Inner4ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Block13 := by
  exact RB4ShiftTerm4.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Band13_eq
#print axioms solution
