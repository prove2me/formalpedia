-- Prove2me | solution 1 for MazurTransfer.order49_recurrence5_exact_integer_field_5
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T12:29:00.185726+00:00
-- url     : https://prove2.me/submissions/4f4f9d18-404f-44c2-b1f0-78bd29088cc0

import Definitions.Def_MazurTransfer_Order49Recurrence5FixedIntegerIntermediatesPart4
import Definitions.Def_MazurTransfer_ExactEqualityCertificate
private theorem fixed_leadingSquare : MazurTransfer.Order49Recurrence5DenseCandidate.leadingSquare = MazurTransfer.Order49Recurrence5DenseCandidate.Fixed.leadingSquare := by
  decide +kernel
private theorem fixed_a3Square : MazurTransfer.Order49Recurrence5DenseCandidate.a3Square = MazurTransfer.Order49Recurrence5DenseCandidate.Fixed.a3Square := by
  decide +kernel
private theorem fixed_quotientConstant : MazurTransfer.Order49Recurrence5DenseCandidate.quotientConstant = MazurTransfer.Order49Recurrence5DenseCandidate.Fixed.quotientConstant := by
  decide +kernel
private theorem fixed_exceptionalProductNumerator : MazurTransfer.Order49Recurrence5DenseCandidate.exceptionalProductNumerator = MazurTransfer.Order49Recurrence5DenseCandidate.Fixed.exceptionalProductNumerator := by
  decide +kernel
private theorem fixed_leadingTimesDividend : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul MazurTransfer.Order49Recurrence5DenseCandidate.b2 MazurTransfer.Order49Recurrence5DenseCandidate.a3 = MazurTransfer.Order49Recurrence5DenseCandidate.Fixed.leadingTimesDividend := by
  decide +kernel
theorem solution : @MazurTransfer.ExactEqualityCertificate (List Int)
  (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scale
    MazurTransfer.Order49Recurrence5DenseCandidate.denominator
    (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul
      MazurTransfer.Order49Recurrence5DenseCandidate.leadingSquare MazurTransfer.Order49Recurrence5DenseCandidate.a1))
  (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.add
    (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.add
      (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scale
        MazurTransfer.Order49Recurrence5DenseCandidate.denominator
        (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul
          MazurTransfer.Order49Recurrence5DenseCandidate.b0
          (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul
            MazurTransfer.Order49Recurrence5DenseCandidate.b2 MazurTransfer.Order49Recurrence5DenseCandidate.a3)))
      (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scale
        MazurTransfer.Order49Recurrence5DenseCandidate.denominator
        (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul
          MazurTransfer.Order49Recurrence5DenseCandidate.b1
          MazurTransfer.Order49Recurrence5DenseCandidate.quotientConstant)))
    (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul
      MazurTransfer.Order49Recurrence5DenseCandidate.exceptionalProductNumerator
      MazurTransfer.Order49Recurrence5DenseCandidate.c1)) := by
  constructor
  rw [fixed_leadingSquare, fixed_quotientConstant, fixed_exceptionalProductNumerator, fixed_leadingTimesDividend]
  decide +kernel
#print axioms solution
