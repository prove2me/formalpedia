-- Prove2me | solution 1 for MazurTransfer.order49_recurrence2_exact_integer_0
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T13:05:54.688457+00:00
-- url     : https://prove2.me/submissions/4143583c-9634-471e-92ff-75c2bc8646fd

import Definitions.Def_MazurTransfer_Order49Recurrence2FixedIntegerIntermediatesPart4
import Definitions.Def_MazurTransfer_ExactEqualityCertificate
private theorem fixed_leadingSquare : MazurTransfer.Order49Recurrence2DenseCandidate.leadingSquare = MazurTransfer.Order49Recurrence2DenseCandidate.Fixed.leadingSquare := by
  decide +kernel
private theorem fixed_a6Square : MazurTransfer.Order49Recurrence2DenseCandidate.a6Square = MazurTransfer.Order49Recurrence2DenseCandidate.Fixed.a6Square := by
  decide +kernel
private theorem fixed_quotientConstant : MazurTransfer.Order49Recurrence2DenseCandidate.quotientConstant = MazurTransfer.Order49Recurrence2DenseCandidate.Fixed.quotientConstant := by
  decide +kernel
private theorem fixed_exceptionalProductNumerator : MazurTransfer.Order49Recurrence2DenseCandidate.exceptionalProductNumerator = MazurTransfer.Order49Recurrence2DenseCandidate.Fixed.exceptionalProductNumerator := by
  decide +kernel
private theorem fixed_leadingTimesDividend : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul MazurTransfer.Order49Recurrence2DenseCandidate.b5 MazurTransfer.Order49Recurrence2DenseCandidate.a6 = MazurTransfer.Order49Recurrence2DenseCandidate.Fixed.leadingTimesDividend := by
  decide +kernel
theorem solution : MazurTransfer.ExactEqualityCertificate (α := List ℤ) ((MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scale MazurTransfer.Order49Recurrence2DenseCandidate.denominator (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul MazurTransfer.Order49Recurrence2DenseCandidate.leadingSquare MazurTransfer.Order49Recurrence2DenseCandidate.a0)) ++ [0]) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.add (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scale MazurTransfer.Order49Recurrence2DenseCandidate.denominator (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul MazurTransfer.Order49Recurrence2DenseCandidate.b0 MazurTransfer.Order49Recurrence2DenseCandidate.quotientConstant)) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul MazurTransfer.Order49Recurrence2DenseCandidate.exceptionalProductNumerator MazurTransfer.Order49Recurrence2DenseCandidate.c0)) := by
  constructor
  rw [fixed_leadingSquare, fixed_quotientConstant, fixed_exceptionalProductNumerator]
  decide +kernel
#print axioms solution
