-- Prove2me | solution 1 for MazurTransfer.order49_recurrence1_divisionCofactor0Coefficient4_eq_normalized
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T06:45:38.674+00:00
-- url     : https://prove2.me/submissions/638bc863-51f1-4864-a8e3-00be50ea1929

import Definitions.Def_MazurTransfer_Order49BacktrackingCofactors
import Definitions.Def_MazurTransfer_Order49Recurrence1NormalizedData
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial
open _root_.MazurTorsion
open _root_.MazurTorsion.Kubert
namespace MazurTransfer.Order49Recurrence1ExistingOriginalChildProofs
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section









theorem divisionCofactor0Coefficient4_eq_normalized :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient4 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source4 := by
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient4 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient4Chunk0
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source4 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source4Block0 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source4Block1
  ring



































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end MazurTransfer.Order49Recurrence1ExistingOriginalChildProofs

theorem solution :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient4 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source4 := by
  exact MazurTransfer.Order49Recurrence1ExistingOriginalChildProofs.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.divisionCofactor0Coefficient4_eq_normalized
#print axioms solution
