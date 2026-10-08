-- Prove2me | solution 1 for MazurTransfer.order49_recurrence5_exact_integer_field_0
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T11:52:12.231139+00:00
-- url     : https://prove2.me/submissions/0d542c31-c23c-4a4a-aff1-80eba991fafa

import Definitions.Def_MazurTransfer_Order49Recurrence5DenseIntegerChunkDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Definitions.Def_MazurTransfer_Order49Recurrence3StandaloneDenseData3
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData5
import Definitions.Def_MazurTransfer_ExactEqualityCertificate
open Polynomial
theorem solution : @MazurTransfer.ExactEqualityCertificate (List Int)
  (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul
    MazurTransfer.Order49Recurrence5DenseCandidate.b2 MazurTransfer.Order49Recurrence5DenseCandidate.b2)
  MazurTransfer.Order49Recurrence5DenseCandidate.leadingSquare := by
  constructor
  rfl
#print axioms solution
