-- Prove2me | solution 1 for MazurTransfer.order49_recurrence1_inner4_ExceptionalTerm4_row_band_recurrence1ExceptionalTerm4Band15_eq
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T10:19:56.488977+00:00
-- url     : https://prove2.me/submissions/059633cd-c9a7-4da5-b5ee-af331e24cde8

import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm4ExactRowBandDataPart0
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm4ExactRowBandDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm4ExactRowBandDataPart2
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm4ExactRowBandDataPart3
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm4ExactRowBandDataPart4
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm4ExactRowBandDataPart5
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm4ExactRowBandDataPart6
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm4ExactRowBandDataPart7
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm4ExactRowBandDataPart8
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner4ExactHelperDataPart3
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial
open _root_.MazurTorsion
open _root_.MazurTorsion.Kubert
namespace RB4ExceptionalTerm4
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section













































































































































































































































































































































































private theorem recurrence1ExceptionalTerm4Band15_eq :
    MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Band15 = MazurTransfer.Order49Recurrence1Inner4ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Block15 := by
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Band15 MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row0Band15
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row1Band15 MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row2Band15
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row3Band15 MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row4Band15
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row5Band15 MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row6Band15
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row7Band15 MazurTransfer.Order49Recurrence1Inner4ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Block15
  ring



































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end RB4ExceptionalTerm4

theorem solution :
    MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Band15 = MazurTransfer.Order49Recurrence1Inner4ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Block15 := by
  exact RB4ExceptionalTerm4.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Band15_eq
#print axioms solution
