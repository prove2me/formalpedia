-- Prove2me | solution 1 for MazurTransfer.order49_recurrence5_exact_integer_field_6
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T11:58:28.772392+00:00
-- url     : https://prove2.me/submissions/31d3835d-de57-4abd-8735-7eef77310f77

import Definitions.Def_MazurTransfer_Order49Recurrence5DenseIntegerChunkDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Definitions.Def_MazurTransfer_Order49Recurrence3StandaloneDenseData3
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData5
import Definitions.Def_MazurTransfer_ExactEqualityCertificate
open Polynomial
theorem solution : @MazurTransfer.ExactEqualityCertificate (List Int) MazurTransfer.Order49Recurrence5DenseCandidate.a0
  MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.c0 := by
  constructor
  decide +kernel
#print axioms solution
