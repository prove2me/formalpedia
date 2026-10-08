-- Prove2me | solution 1 for MazurTransfer.order49_recurrence1_inner5_ExceptionalTerm5_row_band_recurrence1ExceptionalTerm5Band10_eq
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T09:12:20.358718+00:00
-- url     : https://prove2.me/submissions/2ee33a7e-f01f-47ff-9e01-fd0cbe15d57d

import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm5ExactRowBandDataPart0
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm5ExactRowBandDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm5ExactRowBandDataPart2
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm5ExactRowBandDataPart3
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm5ExactRowBandDataPart4
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm5ExactRowBandDataPart5
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm5ExactRowBandDataPart6
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm5ExactRowBandDataPart7
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm5ExactRowBandDataPart8
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner5ExactHelperData
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









































































































































































































































































































































private theorem recurrence1ExceptionalTerm5Band10_eq :
    MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Band10 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Block10 := by
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Band10 MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row0Band10
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row1Band10 MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row2Band10
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row3Band10 MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row4Band10
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row5Band10 MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row6Band10
  unfold MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Row7Band10 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Block10
  ring



















































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end H5

theorem solution :
    MazurTransfer.Order49Recurrence1ExceptionalTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Band10 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Block10 := by
  exact H5.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5Band10_eq
#print axioms solution
