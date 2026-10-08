-- Prove2me | solution 1 for MazurTransfer.order49_recurrence5_exact_integer_field_7
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T11:59:36.819983+00:00
-- url     : https://prove2.me/submissions/839cf6ab-557f-40dd-9300-fc0c4ba8e136

import Definitions.Def_MazurTransfer_Order49Recurrence5DenseIntegerChunkDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Definitions.Def_MazurTransfer_Order49Recurrence3StandaloneDenseData3
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData5
import Definitions.Def_MazurTransfer_ExactEqualityCertificate
open Polynomial
theorem solution : @MazurTransfer.ExactEqualityCertificate (List Int) MazurTransfer.Order49Recurrence5DenseCandidate.a1
  MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.c1 := by
  constructor
  decide +kernel
#print axioms solution
