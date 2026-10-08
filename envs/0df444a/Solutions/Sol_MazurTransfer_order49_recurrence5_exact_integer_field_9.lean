-- Prove2me | solution 1 for MazurTransfer.order49_recurrence5_exact_integer_field_9
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T12:04:57.589337+00:00
-- url     : https://prove2.me/submissions/b6ff4e74-ba74-4b8a-a6f6-830b92931e49

import Definitions.Def_MazurTransfer_Order49Recurrence5DenseIntegerChunkDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Definitions.Def_MazurTransfer_Order49Recurrence3StandaloneDenseData3
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData5
import Definitions.Def_MazurTransfer_ExactEqualityCertificate
open Polynomial
theorem solution : @MazurTransfer.ExactEqualityCertificate (List Int) MazurTransfer.Order49Recurrence5DenseCandidate.a3
  MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.c3 := by
  constructor
  decide +kernel
#print axioms solution
