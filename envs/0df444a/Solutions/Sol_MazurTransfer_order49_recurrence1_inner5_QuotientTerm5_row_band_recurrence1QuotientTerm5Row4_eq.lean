-- Prove2me | solution 1 for MazurTransfer.order49_recurrence1_inner5_QuotientTerm5_row_band_recurrence1QuotientTerm5Row4_eq
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T09:12:22.583015+00:00
-- url     : https://prove2.me/submissions/030188ce-2d87-4ec8-9081-4a3df432b0da

import Definitions.Def_MazurTransfer_Order49Recurrence1NormalizedData
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm5ExactRowBandDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm5ExactRowBandDataPart4
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











































































































































private theorem recurrence1QuotientTerm5Row4_eq :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientConstantBlock4 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25 =
      MazurTransfer.Order49Recurrence1QuotientTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Row4 := by
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientConstantBlock4 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25Block0
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25Block1 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25Block2 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25Block3
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25Block4 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25Block5 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25Block6
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25Block7 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25Block8 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25Block9
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25Block10 MazurTransfer.Order49Recurrence1QuotientTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Row4
  unfold MazurTransfer.Order49Recurrence1QuotientTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Row4Band4 MazurTransfer.Order49Recurrence1QuotientTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Row4Band5
  unfold MazurTransfer.Order49Recurrence1QuotientTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Row4Band6 MazurTransfer.Order49Recurrence1QuotientTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Row4Band7
  unfold MazurTransfer.Order49Recurrence1QuotientTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Row4Band8 MazurTransfer.Order49Recurrence1QuotientTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Row4Band9
  unfold MazurTransfer.Order49Recurrence1QuotientTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Row4Band10 MazurTransfer.Order49Recurrence1QuotientTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Row4Band11
  unfold MazurTransfer.Order49Recurrence1QuotientTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Row4Band12 MazurTransfer.Order49Recurrence1QuotientTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Row4Band13
  unfold MazurTransfer.Order49Recurrence1QuotientTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Row4Band14 MazurTransfer.Order49Recurrence1QuotientTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Row4Band15
  ring







































































































































































































































































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end H5

theorem solution :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientConstantBlock4 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25 =
      MazurTransfer.Order49Recurrence1QuotientTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Row4 := by
  exact H5.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Row4_eq
#print axioms solution
