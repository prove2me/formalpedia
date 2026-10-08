-- Prove2me | solution 1 for MazurTransfer.order49_recurrence5_exact_integer_field_4
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T12:10:00.030996+00:00
-- url     : https://prove2.me/submissions/426f3208-0b59-4779-a774-853c4f20f56f

import Definitions.Def_MazurTransfer_Order49Recurrence5DenseIntegerChunkDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Definitions.Def_MazurTransfer_Order49Recurrence3StandaloneDenseData3
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData5
import Definitions.Def_MazurTransfer_ExactEqualityCertificate
open Polynomial
theorem solution : @MazurTransfer.ExactEqualityCertificate (List Int)
  (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scale
    MazurTransfer.Order49Recurrence5DenseCandidate.denominator
    (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul
      MazurTransfer.Order49Recurrence5DenseCandidate.leadingSquare MazurTransfer.Order49Recurrence5DenseCandidate.a0))
  (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.add
    (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scale
      MazurTransfer.Order49Recurrence5DenseCandidate.denominator
      (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul
        MazurTransfer.Order49Recurrence5DenseCandidate.b0
        MazurTransfer.Order49Recurrence5DenseCandidate.quotientConstant))
    (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul
      MazurTransfer.Order49Recurrence5DenseCandidate.exceptionalProductNumerator
      MazurTransfer.Order49Recurrence5DenseCandidate.c0)) := by
  constructor
  decide +kernel
#print axioms solution
