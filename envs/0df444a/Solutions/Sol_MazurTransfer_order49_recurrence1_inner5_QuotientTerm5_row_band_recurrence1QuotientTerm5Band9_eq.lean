-- Prove2me | solution 1 for MazurTransfer.order49_recurrence1_inner5_QuotientTerm5_row_band_recurrence1QuotientTerm5Band9_eq
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T09:11:41.339593+00:00
-- url     : https://prove2.me/submissions/53a1ac43-d0e2-41bd-a775-09c64497cdbd

import Definitions.Def_MazurTransfer_Order49Recurrence1Inner5ExactHelperData
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm5ExactRowBandDataPart0
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm5ExactRowBandDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm5ExactRowBandDataPart11
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm5ExactRowBandDataPart2
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm5ExactRowBandDataPart3
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm5ExactRowBandDataPart4
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm5ExactRowBandDataPart5
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm5ExactRowBandDataPart6
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm5ExactRowBandDataPart7
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm5ExactRowBandDataPart8
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm5ExactRowBandDataPart9
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



























































































































































































































































































































































private theorem recurrence1QuotientTerm5Band9_eq :
    MazurTransfer.Order49Recurrence1QuotientTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Band9 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Block9 := by
  unfold MazurTransfer.Order49Recurrence1QuotientTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Band9 MazurTransfer.Order49Recurrence1QuotientTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Row0Band9
  unfold MazurTransfer.Order49Recurrence1QuotientTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Row1Band9 MazurTransfer.Order49Recurrence1QuotientTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Row2Band9
  unfold MazurTransfer.Order49Recurrence1QuotientTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Row3Band9 MazurTransfer.Order49Recurrence1QuotientTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Row4Band9
  unfold MazurTransfer.Order49Recurrence1QuotientTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Row5Band9 MazurTransfer.Order49Recurrence1QuotientTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Row6Band9
  unfold MazurTransfer.Order49Recurrence1QuotientTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Row7Band9 MazurTransfer.Order49Recurrence1QuotientTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Row8Band9
  unfold MazurTransfer.Order49Recurrence1QuotientTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Row9Band9 MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Block9
  ring























































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end H5

theorem solution :
    MazurTransfer.Order49Recurrence1QuotientTerm5ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Band9 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Block9 := by
  exact H5.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm5Band9_eq
#print axioms solution
