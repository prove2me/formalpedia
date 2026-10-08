-- Prove2me | solution 1 for MazurTransfer.order49_recurrence1_inner4_ExceptionalTerm4_row_band_recurrence1ExceptionalTerm4Row3_eq
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T11:35:36.358562+00:00
-- url     : https://prove2.me/submissions/7c2825ad-84a4-42d5-804d-dd2b7832112a

import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm4ExactRowBandDataPart0
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm4ExactRowBandDataPart3
import Definitions.Def_MazurTransfer_Order49Recurrence1NormalizedData
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























































































































































private theorem recurrence1ExceptionalTerm4Row3_eq :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalBlock3 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34 =
      MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row3 := by
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalBlock3 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block0
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block1 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block2 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block3
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block4 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block5 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block6
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block7 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block8 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block9
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block10 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block11 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block12
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block13 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block14 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34Block15
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row3 MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row3Band3
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row3Band4 MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row3Band5
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row3Band6 MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row3Band7
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row3Band8 MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row3Band9
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row3Band10 MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row3Band11
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row3Band12 MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row3Band13
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row3Band14 MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row3Band15
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row3Band16 MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row3Band17
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row3Band18 MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row3Band19
  ring

























































































































































































































































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end RB4ExceptionalTerm4

theorem solution :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalBlock3 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34 =
      MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row3 := by
  exact RB4ExceptionalTerm4.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row3_eq
#print axioms solution
