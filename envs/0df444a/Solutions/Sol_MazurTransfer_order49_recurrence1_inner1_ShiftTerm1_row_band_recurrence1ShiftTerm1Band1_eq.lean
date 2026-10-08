-- Prove2me | solution 1 for MazurTransfer.order49_recurrence1_inner1_ShiftTerm1_row_band_recurrence1ShiftTerm1Band1_eq
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T09:56:19.232446+00:00
-- url     : https://prove2.me/submissions/53b3e07d-202b-4db1-8a89-1434fa4dd455

import Definitions.Def_MazurTransfer_Order49Recurrence1Inner1ExactHelperDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm1ExactRowBandDataPart0
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm1ExactRowBandDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm1ExactRowBandDataPart11
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial
open _root_.MazurTorsion
open _root_.MazurTorsion.Kubert
namespace RB1ShiftTerm1
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section







theorem recurrence1ShiftTerm1Band1_eq :
    MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Band1 = MazurTransfer.Order49Recurrence1Inner1ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Block1 := by
  unfold MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Band1 MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row0Band1 MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Row1Band1
  unfold MazurTransfer.Order49Recurrence1Inner1ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Block1
  ring









































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end RB1ShiftTerm1

theorem solution :
    MazurTransfer.Order49Recurrence1ShiftTerm1ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Band1 = MazurTransfer.Order49Recurrence1Inner1ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Block1 := by
  exact RB1ShiftTerm1.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1Band1_eq
#print axioms solution
