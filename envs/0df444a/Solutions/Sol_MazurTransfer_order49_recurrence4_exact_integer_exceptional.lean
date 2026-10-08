-- Prove2me | solution 1 for MazurTransfer.order49_recurrence4_exact_integer_exceptional
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T12:03:30.66638+00:00
-- url     : https://prove2.me/submissions/1ff11090-8307-43a8-abaf-15af6ef1b047

import Definitions.Def_MazurTransfer_Order49Recurrence4ReusedDenseIntegerDataWithExtraTables
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData4
import Definitions.Def_MazurTransfer_ExactEqualityCertificate
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
open Polynomial
theorem solution : MazurTransfer.ExactEqualityCertificate (α := Polynomial ℚ) (C (MazurTransfer.Order49Recurrence4DenseCandidate.denominator : ℚ) * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional4) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence4DenseCandidate.exceptionalNumerator) := by
  constructor
  have hunit : C (MazurTransfer.Order49Recurrence4DenseCandidate.denominator : ℚ) * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptionalUnit4 = 1 := by
    unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptionalUnit4 MazurTransfer.Order49Recurrence4DenseCandidate.denominator
    rw [← map_mul]
    norm_num
  simp only [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional4, ← mul_assoc, hunit, one_mul]
  unfold MazurTransfer.Order49Recurrence4DenseCandidate.exceptionalNumerator
  simp only [MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial, map_intCast]
  norm_num [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.parameter, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.discriminantFactor, map_ofNat, map_neg]
  ring
#print axioms solution
