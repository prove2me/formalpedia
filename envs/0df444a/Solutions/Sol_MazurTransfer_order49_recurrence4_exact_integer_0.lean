-- Prove2me | solution 1 for MazurTransfer.order49_recurrence4_exact_integer_0
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T12:20:13.352976+00:00
-- url     : https://prove2.me/submissions/cd9a6bcb-ceec-4860-939b-f0d533a98943

import Definitions.Def_MazurTransfer_Order49Recurrence4FixedIntegerIntermediatesPart4
import Definitions.Def_MazurTransfer_ExactEqualityCertificate
private theorem fixed_leadingSquare : MazurTransfer.Order49Recurrence4DenseCandidate.leadingSquare = MazurTransfer.Order49Recurrence4DenseCandidate.Fixed.leadingSquare := by
  decide +kernel
private theorem fixed_a4Square : MazurTransfer.Order49Recurrence4DenseCandidate.a4Square = MazurTransfer.Order49Recurrence4DenseCandidate.Fixed.a4Square := by
  decide +kernel
private theorem fixed_quotientConstant : MazurTransfer.Order49Recurrence4DenseCandidate.quotientConstant = MazurTransfer.Order49Recurrence4DenseCandidate.Fixed.quotientConstant := by
  decide +kernel
private theorem fixed_exceptionalProductNumerator : MazurTransfer.Order49Recurrence4DenseCandidate.exceptionalProductNumerator = MazurTransfer.Order49Recurrence4DenseCandidate.Fixed.exceptionalProductNumerator := by
  decide +kernel
private theorem fixed_leadingTimesDividend : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul MazurTransfer.Order49Recurrence4DenseCandidate.b3 MazurTransfer.Order49Recurrence4DenseCandidate.a4 = MazurTransfer.Order49Recurrence4DenseCandidate.Fixed.leadingTimesDividend := by
  decide +kernel
theorem solution : MazurTransfer.ExactEqualityCertificate (α := List ℤ) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scale MazurTransfer.Order49Recurrence4DenseCandidate.denominator (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul MazurTransfer.Order49Recurrence4DenseCandidate.leadingSquare MazurTransfer.Order49Recurrence4DenseCandidate.a0)) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.add (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scale MazurTransfer.Order49Recurrence4DenseCandidate.denominator (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul MazurTransfer.Order49Recurrence4DenseCandidate.b0 MazurTransfer.Order49Recurrence4DenseCandidate.quotientConstant)) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul MazurTransfer.Order49Recurrence4DenseCandidate.exceptionalProductNumerator MazurTransfer.Order49Recurrence4DenseCandidate.c0)) := by
  constructor
  rw [fixed_leadingSquare, fixed_quotientConstant, fixed_exceptionalProductNumerator]
  decide +kernel
#print axioms solution
