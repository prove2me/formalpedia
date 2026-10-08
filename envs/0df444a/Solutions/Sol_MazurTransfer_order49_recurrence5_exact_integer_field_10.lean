-- Prove2me | solution 1 for MazurTransfer.order49_recurrence5_exact_integer_field_10
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T12:08:52.432984+00:00
-- url     : https://prove2.me/submissions/de2a4152-aaf9-45a0-bc7a-6375cc17a4b9

import Definitions.Def_MazurTransfer_ExactEqualityCertificate
import Definitions.Def_MazurTransfer_Order49Recurrence5DenseIntegerChunkDataPart1
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData5
import Definitions.Def_MazurTransfer_Order49Recurrence3StandaloneDenseData3
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
open Polynomial
namespace MazurTransfer.Order49Recurrence5DenseCandidate
theorem exceptional_integer_interpretation :
  C (denominator : ℚ) * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional5 = MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial exceptionalNumerator := by
  have hunit : C (denominator : ℚ) * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptionalUnit5 = 1 := by
    unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptionalUnit5 denominator
    rw [← map_mul]
    norm_num
  simp only [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional5, ← mul_assoc, hunit, one_mul]
  unfold exceptionalNumerator
  simp only [MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial, map_intCast]
  norm_num [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.parameter, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.discriminantFactor, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.cmSix, map_ofNat, map_neg]
  ring
#print axioms exceptional_integer_interpretation
end MazurTransfer.Order49Recurrence5DenseCandidate

theorem solution : @MazurTransfer.ExactEqualityCertificate (@Polynomial Rat Rat.semiring)
  (@HMul.hMul (@Polynomial Rat Rat.semiring)
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient
    (@Polynomial Rat Rat.semiring) (@instHMul (@Polynomial Rat Rat.semiring) (@Polynomial.instMul Rat Rat.semiring))
    (@DFunLike.coe
      (@RingHom Rat (@Polynomial Rat Rat.semiring) (@Semiring.toNonAssocSemiring Rat Rat.semiring)
        (@Semiring.toNonAssocSemiring (@Polynomial Rat Rat.semiring) (@Polynomial.semiring Rat Rat.semiring)))
      Rat (fun x => @Polynomial Rat Rat.semiring)
      (@RingHom.instFunLike Rat (@Polynomial Rat Rat.semiring) (@Semiring.toNonAssocSemiring Rat Rat.semiring)
        (@Semiring.toNonAssocSemiring (@Polynomial Rat Rat.semiring) (@Polynomial.semiring Rat Rat.semiring)))
      (@Polynomial.C Rat Rat.semiring)
      (@Int.cast Rat Rat.instIntCast MazurTransfer.Order49Recurrence5DenseCandidate.denominator))
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional5)
  (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial
    MazurTransfer.Order49Recurrence5DenseCandidate.exceptionalNumerator) := by
  exact ⟨MazurTransfer.Order49Recurrence5DenseCandidate.exceptional_integer_interpretation⟩
#print axioms solution
