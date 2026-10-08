-- Prove2me | solution 1 for MazurTransfer.order49_recurrence1_inner5_ExceptionalTerm5_row_band_recurrence1ExceptionalTerm5Row3_eq
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T09:11:22.875698+00:00
-- url     : https://prove2.me/submissions/719533de-0ef7-4f42-8f42-9a931e2f42a6

import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm5ExactRowBandDataPart0
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm5ExactRowBandDataPart2
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm5ExactRowBandDataPart3
import Definitions.Def_MazurTransfer_Order49Recurrence1NormalizedData
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















































































































































private theorem recurrence1ExceptionalTerm5Row3_eq :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalBlock3 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35 =
      MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row3 := by
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalBlock3 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block0
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block1 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block2 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block3
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block4 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block5 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block6
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block7 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block8 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block9
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block10 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block11 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block12
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block13 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35Block14 MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row3
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row3Band3 MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row3Band4
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row3Band5 MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row3Band6
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row3Band7 MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row3Band8
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row3Band9 MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row3Band10
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row3Band11 MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row3Band12
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row3Band13 MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row3Band14
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row3Band15 MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row3Band16
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row3Band17 MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row3Band18
  ring













































































































































































































































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end H5

theorem solution :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalBlock3 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35 =
      MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row3 := by
  exact H5.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row3_eq
#print axioms solution
