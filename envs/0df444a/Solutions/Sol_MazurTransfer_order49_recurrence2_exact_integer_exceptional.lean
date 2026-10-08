-- Prove2me | solution 1 for MazurTransfer.order49_recurrence2_exact_integer_exceptional
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T13:03:08.013296+00:00
-- url     : https://prove2.me/submissions/a76e3f20-829d-4c26-912b-0bfb6b970a28

import Definitions.Def_MazurTransfer_Order49Recurrence2ReusedDenseIntegerData
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData2
import Definitions.Def_MazurTransfer_ExactEqualityCertificate
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
open Polynomial
theorem solution : MazurTransfer.ExactEqualityCertificate (α := Polynomial ℚ) (C (MazurTransfer.Order49Recurrence2DenseCandidate.denominator : ℚ) * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional2) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.exceptionalNumerator) := by
  constructor
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional2 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptionalUnit2 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.parameter MazurTransfer.Order49Recurrence2DenseCandidate.denominator MazurTransfer.Order49Recurrence2DenseCandidate.exceptionalNumerator
  simp only [MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial, map_intCast, map_ofNat, map_neg]
  norm_num <;> ring
#print axioms solution
