-- Prove2me | solution 1 for MazurTransfer.order49_scalarResidual4Coefficient2_parametric_exact_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T12:41:37.342384+00:00
-- url     : https://prove2.me/submissions/a3947b23-6e19-4564-9071-48269a4818a7

import Theorems.Thm_MazurTransfer_order49_recurrence4_exact_integer_exceptional
import Theorems.Thm_MazurTransfer_order49_recurrence4_exact_integer_0
import Theorems.Thm_MazurTransfer_order49_recurrence4_exact_integer_1
import Theorems.Thm_MazurTransfer_order49_recurrence4_exact_integer_2
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_add
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_mul
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_scale
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_b0
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_b1
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_b2
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_b3
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_b4
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_c0
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_c1
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_c2
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_c3
import Theorems.Thm_MazurTransfer_order49_recurrence5_five_full_integer_table_interpretations
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
open Polynomial
private theorem scalar0_of_cleared_identity
    (d a0 a3 a4 b0 b2 b3 c0 e : Polynomial ℚ) (hd : d ≠ 0)
    (h : d * ((b3 * b3) * a0) =
      d * (b0 * (b3 * a3 - b2 * a4)) + (a4 * a4 * (d * e)) * c0) :
    b3 ^ 2 * a0 = b0 * (b3 * a3 - b2 * a4) + a4 ^ 2 * e * c0 := by
  apply mul_left_cancel₀ hd
  calc
    d * (b3 ^ 2 * a0) = d * ((b3 * b3) * a0) := by ring
    _ = d * (b0 * (b3 * a3 - b2 * a4)) + (a4 * a4 * (d * e)) * c0 := h
    _ = d * (b0 * (b3 * a3 - b2 * a4) + a4 ^ 2 * e * c0) := by ring

private theorem scalar_positive_of_cleared_identity
    (d a a3 a4 bprev bcurrent b2 b3 c e : Polynomial ℚ) (hd : d ≠ 0)
    (h : d * ((b3 * b3) * a) =
      (d * (bprev * (b3 * a4)) + d * (bcurrent * (b3 * a3 - b2 * a4))) +
        (a4 * a4 * (d * e)) * c) :
    b3 ^ 2 * a = bprev * b3 * a4 + bcurrent * (b3 * a3 - b2 * a4) + a4 ^ 2 * e * c := by
  apply mul_left_cancel₀ hd
  calc
    d * (b3 ^ 2 * a) = d * ((b3 * b3) * a) := by ring
    _ = (d * (bprev * (b3 * a4)) + d * (bcurrent * (b3 * a3 - b2 * a4))) +
        (a4 * a4 * (d * e)) * c := h
    _ = d * (bprev * b3 * a4 + bcurrent * (b3 * a3 - b2 * a4) + a4 ^ 2 * e * c) := by ring

private theorem input_a0 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence4DenseCandidate.a0 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient0 := by
  simpa only [MazurTransfer.Order49Recurrence4DenseCandidate.a0] using MazurTransfer.order49_recurrence3_toPolynomial_b0
private theorem input_a1 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence4DenseCandidate.a1 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient1 := by
  simpa only [MazurTransfer.Order49Recurrence4DenseCandidate.a1] using MazurTransfer.order49_recurrence3_toPolynomial_b1
private theorem input_a2 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence4DenseCandidate.a2 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient2 := by
  simpa only [MazurTransfer.Order49Recurrence4DenseCandidate.a2] using MazurTransfer.order49_recurrence3_toPolynomial_b2
private theorem input_a3 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence4DenseCandidate.a3 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient3 := by
  simpa only [MazurTransfer.Order49Recurrence4DenseCandidate.a3] using MazurTransfer.order49_recurrence3_toPolynomial_b3
private theorem input_a4 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence4DenseCandidate.a4 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient4 := by
  simpa only [MazurTransfer.Order49Recurrence4DenseCandidate.a4] using MazurTransfer.order49_recurrence3_toPolynomial_b4
private theorem input_b0 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence4DenseCandidate.b0 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient0 := by
  simpa only [MazurTransfer.Order49Recurrence4DenseCandidate.b0] using MazurTransfer.order49_recurrence3_toPolynomial_c0
private theorem input_b1 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence4DenseCandidate.b1 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient1 := by
  simpa only [MazurTransfer.Order49Recurrence4DenseCandidate.b1] using MazurTransfer.order49_recurrence3_toPolynomial_c1
private theorem input_b2 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence4DenseCandidate.b2 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2 := by
  simpa only [MazurTransfer.Order49Recurrence4DenseCandidate.b2] using MazurTransfer.order49_recurrence3_toPolynomial_c2
private theorem input_b3 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence4DenseCandidate.b3 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient3 := by
  simpa only [MazurTransfer.Order49Recurrence4DenseCandidate.b3] using MazurTransfer.order49_recurrence3_toPolynomial_c3
private theorem input_c0 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence4DenseCandidate.c0 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0 := by
  simpa only [MazurTransfer.Order49Recurrence4DenseCandidate.c0] using MazurTransfer.order49_recurrence5_five_full_integer_table_interpretations.1.identity
private theorem input_c1 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence4DenseCandidate.c1 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient1 := by
  simpa only [MazurTransfer.Order49Recurrence4DenseCandidate.c1] using MazurTransfer.order49_recurrence5_five_full_integer_table_interpretations.2.1.identity
private theorem input_c2 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence4DenseCandidate.c2 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2 := by
  simpa only [MazurTransfer.Order49Recurrence4DenseCandidate.c2] using MazurTransfer.order49_recurrence5_five_full_integer_table_interpretations.2.2.1.identity
private theorem leading_polynomial : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence4DenseCandidate.leadingSquare = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient3 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient3 := by
  rw [MazurTransfer.Order49Recurrence4DenseCandidate.leadingSquare, MazurTransfer.order49_recurrence3_toPolynomial_mul, input_b3]
private theorem quotient_polynomial : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence4DenseCandidate.quotientConstant = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient3 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient3 - MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient4 := by
  simp only [MazurTransfer.Order49Recurrence4DenseCandidate.quotientConstant, MazurTransfer.order49_recurrence3_toPolynomial_add, MazurTransfer.order49_recurrence3_toPolynomial_mul, MazurTransfer.order49_recurrence3_toPolynomial_scale, input_b3, input_a3, input_b2, input_a4]
  norm_num
  simp only [neg_one_mul, sub_eq_add_neg]
private theorem exceptional_polynomial : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence4DenseCandidate.exceptionalProductNumerator = (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient4 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient4) * (C (MazurTransfer.Order49Recurrence4DenseCandidate.denominator : ℚ) * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional4) := by
  rw [MazurTransfer.Order49Recurrence4DenseCandidate.exceptionalProductNumerator, MazurTransfer.order49_recurrence3_toPolynomial_mul, MazurTransfer.Order49Recurrence4DenseCandidate.a4Square, MazurTransfer.order49_recurrence3_toPolynomial_mul, input_a4, ← MazurTransfer.order49_recurrence4_exact_integer_exceptional.identity]
private theorem denominator_nonzero : C (MazurTransfer.Order49Recurrence4DenseCandidate.denominator : ℚ) ≠ (0 : Polynomial ℚ) := by
  rw [Polynomial.C_ne_zero]
  norm_num [MazurTransfer.Order49Recurrence4DenseCandidate.denominator]
theorem solution : MazurTransfer.ExactEqualityCertificate (α := Polynomial ℚ)
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient3 ^ 2 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient2)
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient1 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient3 *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient4 +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient3 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient3 -
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient4) +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient4 ^ 2 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional4 *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2) := by
  constructor
  have hscaled := congrArg MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial (MazurTransfer.order49_recurrence4_exact_integer_2.identity)
  simp only [MazurTransfer.order49_recurrence3_toPolynomial_add, MazurTransfer.order49_recurrence3_toPolynomial_mul, MazurTransfer.order49_recurrence3_toPolynomial_scale, leading_polynomial, quotient_polynomial, exceptional_polynomial, input_a2, input_a4, input_b0, input_b1, input_b2, input_b3, input_c2] at hscaled
  exact scalar_positive_of_cleared_identity (C (MazurTransfer.Order49Recurrence4DenseCandidate.denominator : ℚ)) MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient2 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient3 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient4 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient1 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient3 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional4 denominator_nonzero hscaled
#print axioms solution
