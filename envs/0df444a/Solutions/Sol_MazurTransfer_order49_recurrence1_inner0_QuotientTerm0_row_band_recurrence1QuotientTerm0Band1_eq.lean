-- Prove2me | solution 1 for MazurTransfer.order49_recurrence1_inner0_QuotientTerm0_row_band_recurrence1QuotientTerm0Band1_eq
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T09:48:32.967526+00:00
-- url     : https://prove2.me/submissions/3152f359-cfb3-4814-8b48-522d8bf8d1ae

import Definitions.Def_MazurTransfer_Order49Recurrence1Inner0ExactHelperDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm0ExactRowBandDataPart0
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm0ExactRowBandDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence1QuotientTerm0ExactRowBandDataPart11
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial
open _root_.MazurTorsion
open _root_.MazurTorsion.Kubert
namespace RB0QuotientTerm0
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section







theorem recurrence1QuotientTerm0Band1_eq :
    MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Band1 = MazurTransfer.Order49Recurrence1Inner0ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Block1 := by
  unfold MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Band1 MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row0Band1
  unfold MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Row1Band1 MazurTransfer.Order49Recurrence1Inner0ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Block1
  ring













































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end RB0QuotientTerm0

theorem solution :
    MazurTransfer.Order49Recurrence1QuotientTerm0ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Band1 = MazurTransfer.Order49Recurrence1Inner0ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Block1 := by
  exact RB0QuotientTerm0.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm0Band1_eq
#print axioms solution
