-- Prove2me | solution 1 for MazurTransfer.order49_recurrence5_exact_integer_field_8
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T12:03:28.169678+00:00
-- url     : https://prove2.me/submissions/657bb736-f012-4481-8daf-fc22056d4198

import Definitions.Def_MazurTransfer_Order49Recurrence5DenseIntegerChunkDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Definitions.Def_MazurTransfer_Order49Recurrence3StandaloneDenseData3
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData5
import Definitions.Def_MazurTransfer_ExactEqualityCertificate
open Polynomial
theorem solution : @MazurTransfer.ExactEqualityCertificate (List Int) MazurTransfer.Order49Recurrence5DenseCandidate.a2
  MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.c2 := by
  constructor
  decide +kernel
#print axioms solution
