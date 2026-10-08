-- Prove2me | solution 1 for MazurTransfer.order49_scalarResidual5Coefficient1_parametric_exact_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T11:53:03.048342+00:00
-- url     : https://prove2.me/submissions/0fee7047-d186-4ec3-a01e-ee55db19f330

import Theorems.Thm_MazurTransfer_order49_recurrence5_five_full_integer_table_interpretations
import Theorems.Thm_MazurTransfer_order49_recurrence5_dense_integer_certificates_and_anchors
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_add
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_mul
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_scale
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_c0
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_c1
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_c2
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_c3
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
open Polynomial
private theorem scalar0_of_cleared_identity
    (d a0 a2 a3 b0 b1 b2 c0 e : Polynomial ℚ) (hd : d ≠ 0)
    (h : d * ((b2 * b2) * a0) =
      d * (b0 * (b2 * a2 - b1 * a3)) + (a3 * a3 * (d * e)) * c0) :
    b2 ^ 2 * a0 = b0 * (b2 * a2 - b1 * a3) + a3 ^ 2 * e * c0 := by
  apply mul_left_cancel₀ hd
  calc
    d * (b2 ^ 2 * a0) = d * ((b2 * b2) * a0) := by ring
    _ = d * (b0 * (b2 * a2 - b1 * a3)) + (a3 * a3 * (d * e)) * c0 := h
    _ = d * (b0 * (b2 * a2 - b1 * a3) + a3 ^ 2 * e * c0) := by ring

private theorem scalar1_of_cleared_identity
    (d a1 a2 a3 b0 b1 b2 c1 e : Polynomial ℚ) (hd : d ≠ 0)
    (h : d * ((b2 * b2) * a1) =
      (d * (b0 * (b2 * a3)) + d * (b1 * (b2 * a2 - b1 * a3))) +
        (a3 * a3 * (d * e)) * c1) :
    b2 ^ 2 * a1 = b0 * b2 * a3 + b1 * (b2 * a2 - b1 * a3) + a3 ^ 2 * e * c1 := by
  apply mul_left_cancel₀ hd
  calc
    d * (b2 ^ 2 * a1) = d * ((b2 * b2) * a1) := by ring
    _ = (d * (b0 * (b2 * a3)) + d * (b1 * (b2 * a2 - b1 * a3))) +
        (a3 * a3 * (d * e)) * c1 := h
    _ = d * (b0 * b2 * a3 + b1 * (b2 * a2 - b1 * a3) + a3 ^ 2 * e * c1) := by ring

private theorem input_a0 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence5DenseCandidate.a0 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient0 := by
  rw [MazurTransfer.order49_recurrence5_dense_integer_certificates_and_anchors.2.2.2.2.2.2.1.identity]
  exact MazurTransfer.order49_recurrence3_toPolynomial_c0
private theorem input_a1 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence5DenseCandidate.a1 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient1 := by
  rw [MazurTransfer.order49_recurrence5_dense_integer_certificates_and_anchors.2.2.2.2.2.2.2.1.identity]
  exact MazurTransfer.order49_recurrence3_toPolynomial_c1
private theorem input_a2 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence5DenseCandidate.a2 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2 := by
  rw [MazurTransfer.order49_recurrence5_dense_integer_certificates_and_anchors.2.2.2.2.2.2.2.2.1.identity]
  exact MazurTransfer.order49_recurrence3_toPolynomial_c2
private theorem input_a3 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence5DenseCandidate.a3 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient3 := by
  rw [MazurTransfer.order49_recurrence5_dense_integer_certificates_and_anchors.2.2.2.2.2.2.2.2.2.1.identity]
  exact MazurTransfer.order49_recurrence3_toPolynomial_c3
private theorem input_b0 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence5DenseCandidate.b0 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0 := MazurTransfer.order49_recurrence5_five_full_integer_table_interpretations.1.identity
private theorem input_b1 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence5DenseCandidate.b1 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient1 := MazurTransfer.order49_recurrence5_five_full_integer_table_interpretations.2.1.identity
private theorem input_b2 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence5DenseCandidate.b2 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2 := MazurTransfer.order49_recurrence5_five_full_integer_table_interpretations.2.2.1.identity
private theorem input_c0 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence5DenseCandidate.c0 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0 := MazurTransfer.order49_recurrence5_five_full_integer_table_interpretations.2.2.2.1.identity
private theorem input_c1 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence5DenseCandidate.c1 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1 := MazurTransfer.order49_recurrence5_five_full_integer_table_interpretations.2.2.2.2.identity
private theorem leading_polynomial : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence5DenseCandidate.leadingSquare = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2 := by
  rw [← MazurTransfer.order49_recurrence5_dense_integer_certificates_and_anchors.1.identity, MazurTransfer.order49_recurrence3_toPolynomial_mul, input_b2]
private theorem square_polynomial : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence5DenseCandidate.a3Square = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient3 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient3 := by
  rw [← MazurTransfer.order49_recurrence5_dense_integer_certificates_and_anchors.2.1.identity, MazurTransfer.order49_recurrence3_toPolynomial_mul, input_a3]
private theorem quotient_polynomial : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence5DenseCandidate.quotientConstant = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2 - MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient1 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient3 := by
  rw [← MazurTransfer.order49_recurrence5_dense_integer_certificates_and_anchors.2.2.1.identity]
  simp only [MazurTransfer.order49_recurrence3_toPolynomial_add, MazurTransfer.order49_recurrence3_toPolynomial_mul, MazurTransfer.order49_recurrence3_toPolynomial_scale, input_b2, input_a2, input_b1, input_a3]
  norm_num
  simp only [neg_one_mul, sub_eq_add_neg]
private theorem exceptional_polynomial : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence5DenseCandidate.exceptionalProductNumerator = (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient3 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient3) * (C (MazurTransfer.Order49Recurrence5DenseCandidate.denominator : ℚ) * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional5) := by
  rw [← MazurTransfer.order49_recurrence5_dense_integer_certificates_and_anchors.2.2.2.1.identity, MazurTransfer.order49_recurrence3_toPolynomial_mul, square_polynomial, ← MazurTransfer.order49_recurrence5_dense_integer_certificates_and_anchors.2.2.2.2.2.2.2.2.2.2.identity]
private theorem denominator_nonzero : C (MazurTransfer.Order49Recurrence5DenseCandidate.denominator : ℚ) ≠ (0 : Polynomial ℚ) := by
  rw [Polynomial.C_ne_zero]
  norm_num [MazurTransfer.Order49Recurrence5DenseCandidate.denominator]

theorem solution : MazurTransfer.ExactEqualityCertificate (α := Polynomial ℚ)
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2 ^ 2 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient1)
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2 *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient3 +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient1 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2 -
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient1 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient3) +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient3 ^ 2 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional5 *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1) := by
  constructor
  have hscaled := congrArg MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial (MazurTransfer.order49_recurrence5_dense_integer_certificates_and_anchors.2.2.2.2.2.1.identity)
  simp only [MazurTransfer.order49_recurrence3_toPolynomial_add, MazurTransfer.order49_recurrence3_toPolynomial_mul, MazurTransfer.order49_recurrence3_toPolynomial_scale, leading_polynomial, quotient_polynomial, exceptional_polynomial, input_a1, input_a3, input_b0, input_b1, input_b2, input_c1] at hscaled
  exact scalar1_of_cleared_identity (C (MazurTransfer.Order49Recurrence5DenseCandidate.denominator : ℚ)) MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient1 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient3 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient1 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional5 denominator_nonzero hscaled
#print axioms solution
