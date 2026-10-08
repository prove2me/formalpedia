-- Prove2me | solution 1 for MazurTransfer.order49_recurrence5_exact_integer_field_2
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T11:55:30.941432+00:00
-- url     : https://prove2.me/submissions/101c2e54-2436-4fac-9d2a-9f04fcc46564

import Definitions.Def_MazurTransfer_Order49Recurrence5DenseIntegerChunkDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Definitions.Def_MazurTransfer_Order49Recurrence3StandaloneDenseData3
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData5
import Definitions.Def_MazurTransfer_ExactEqualityCertificate
open Polynomial
theorem solution : @MazurTransfer.ExactEqualityCertificate (List Int)
  (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.add
    (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul
      MazurTransfer.Order49Recurrence5DenseCandidate.b2 MazurTransfer.Order49Recurrence5DenseCandidate.a2)
    (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scale
      (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul
        MazurTransfer.Order49Recurrence5DenseCandidate.b1 MazurTransfer.Order49Recurrence5DenseCandidate.a3)))
  MazurTransfer.Order49Recurrence5DenseCandidate.quotientConstant := by
  constructor
  rfl
#print axioms solution
