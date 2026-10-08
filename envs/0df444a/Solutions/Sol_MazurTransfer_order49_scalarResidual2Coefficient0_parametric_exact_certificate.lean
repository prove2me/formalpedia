-- Prove2me | solution 1 for MazurTransfer.order49_scalarResidual2Coefficient0_parametric_exact_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T13:28:00.128983+00:00
-- url     : https://prove2.me/submissions/5330a65f-4e14-444d-b7a7-adaf4ea5569f

import Theorems.Thm_MazurTransfer_order49_recurrence2_exact_integer_0
import Theorems.Thm_MazurTransfer_order49_recurrence2_exact_integer_1
import Theorems.Thm_MazurTransfer_order49_recurrence2_exact_integer_2
import Theorems.Thm_MazurTransfer_order49_recurrence2_exact_integer_3
import Theorems.Thm_MazurTransfer_order49_recurrence2_exact_integer_4
import Theorems.Thm_MazurTransfer_order49_recurrence2_exact_integer_exceptional
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_add
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_mul
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_scale
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_a0
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_a1
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_a2
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_a3
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_a4
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_a5
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_b0
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_b1
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_b2
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_b3
import Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_b4
import Theorems.Thm_MazurTransfer_order49_recurrence2_seven_full_dividend_integer_interpretations
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
    b3 ^ 2 * a = bprev * (b3 * a4) + bcurrent * (b3 * a3 - b2 * a4) + a4 ^ 2 * e * c := by
  apply mul_left_cancel₀ hd
  calc
    d * (b3 ^ 2 * a) = d * ((b3 * b3) * a) := by ring
    _ = (d * (bprev * (b3 * a4)) + d * (bcurrent * (b3 * a3 - b2 * a4))) +
        (a4 * a4 * (d * e)) * c := h
    _ = d * (bprev * (b3 * a4) + bcurrent * (b3 * a3 - b2 * a4) + a4 ^ 2 * e * c) := by ring

private theorem toPolynomial_append_single_zero (xs : List ℤ) : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial (xs ++ [0]) = MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial xs := by
  induction xs with
  | nil => simp [MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial]
  | cons x xs ih => simp only [List.cons_append, MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial, ih]
private theorem input_a0 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.a0 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient0 := MazurTransfer.order49_recurrence2_seven_full_dividend_integer_interpretations.1.identity
private theorem input_a1 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.a1 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient1 := MazurTransfer.order49_recurrence2_seven_full_dividend_integer_interpretations.2.1.identity
private theorem input_a2 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.a2 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient2 := MazurTransfer.order49_recurrence2_seven_full_dividend_integer_interpretations.2.2.1.identity
private theorem input_a3 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.a3 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient3 := MazurTransfer.order49_recurrence2_seven_full_dividend_integer_interpretations.2.2.2.1.identity
private theorem input_a4 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.a4 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient4 := MazurTransfer.order49_recurrence2_seven_full_dividend_integer_interpretations.2.2.2.2.1.identity
private theorem input_a5 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.a5 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5 := MazurTransfer.order49_recurrence2_seven_full_dividend_integer_interpretations.2.2.2.2.2.1.identity
private theorem input_a6 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.a6 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 := MazurTransfer.order49_recurrence2_seven_full_dividend_integer_interpretations.2.2.2.2.2.2.identity
private theorem input_b0 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.b0 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient0 := by
  simpa only [MazurTransfer.Order49Recurrence2DenseCandidate.b0] using MazurTransfer.order49_recurrence3_toPolynomial_a0
private theorem input_b1 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.b1 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient1 := by
  simpa only [MazurTransfer.Order49Recurrence2DenseCandidate.b1] using MazurTransfer.order49_recurrence3_toPolynomial_a1
private theorem input_b2 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.b2 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient2 := by
  simpa only [MazurTransfer.Order49Recurrence2DenseCandidate.b2] using MazurTransfer.order49_recurrence3_toPolynomial_a2
private theorem input_b3 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.b3 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient3 := by
  simpa only [MazurTransfer.Order49Recurrence2DenseCandidate.b3] using MazurTransfer.order49_recurrence3_toPolynomial_a3
private theorem input_b4 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.b4 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient4 := by
  simpa only [MazurTransfer.Order49Recurrence2DenseCandidate.b4] using MazurTransfer.order49_recurrence3_toPolynomial_a4
private theorem input_b5 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.b5 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient5 := by
  simpa only [MazurTransfer.Order49Recurrence2DenseCandidate.b5] using MazurTransfer.order49_recurrence3_toPolynomial_a5
private theorem input_c0 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.c0 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient0 := by
  simpa only [MazurTransfer.Order49Recurrence2DenseCandidate.c0] using MazurTransfer.order49_recurrence3_toPolynomial_b0
private theorem input_c1 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.c1 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient1 := by
  simpa only [MazurTransfer.Order49Recurrence2DenseCandidate.c1] using MazurTransfer.order49_recurrence3_toPolynomial_b1
private theorem input_c2 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.c2 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient2 := by
  simpa only [MazurTransfer.Order49Recurrence2DenseCandidate.c2] using MazurTransfer.order49_recurrence3_toPolynomial_b2
private theorem input_c3 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.c3 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient3 := by
  simpa only [MazurTransfer.Order49Recurrence2DenseCandidate.c3] using MazurTransfer.order49_recurrence3_toPolynomial_b3
private theorem input_c4 : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.c4 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient4 := by
  simpa only [MazurTransfer.Order49Recurrence2DenseCandidate.c4] using MazurTransfer.order49_recurrence3_toPolynomial_b4
private theorem leading_polynomial : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.leadingSquare = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient5 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient5 := by
  rw [MazurTransfer.Order49Recurrence2DenseCandidate.leadingSquare, MazurTransfer.order49_recurrence3_toPolynomial_mul, input_b5]
private theorem quotient_polynomial : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.quotientConstant = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient5 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5 - MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient4 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 := by
  simp only [MazurTransfer.Order49Recurrence2DenseCandidate.quotientConstant, MazurTransfer.order49_recurrence3_toPolynomial_add, MazurTransfer.order49_recurrence3_toPolynomial_mul, MazurTransfer.order49_recurrence3_toPolynomial_scale, input_b5, input_a5, input_b4, input_a6]
  norm_num
  simp only [neg_one_mul, sub_eq_add_neg]
private theorem exceptional_polynomial : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.exceptionalProductNumerator = (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6) * (C (MazurTransfer.Order49Recurrence2DenseCandidate.denominator : ℚ) * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional2) := by
  rw [MazurTransfer.Order49Recurrence2DenseCandidate.exceptionalProductNumerator, MazurTransfer.order49_recurrence3_toPolynomial_mul, MazurTransfer.Order49Recurrence2DenseCandidate.a6Square, MazurTransfer.order49_recurrence3_toPolynomial_mul, input_a6, ← MazurTransfer.order49_recurrence2_exact_integer_exceptional.identity]
private theorem denominator_nonzero : C (MazurTransfer.Order49Recurrence2DenseCandidate.denominator : ℚ) ≠ (0 : Polynomial ℚ) := by
  rw [Polynomial.C_ne_zero]
  norm_num [MazurTransfer.Order49Recurrence2DenseCandidate.denominator]
theorem solution : MazurTransfer.ExactEqualityCertificate (α := Polynomial ℚ)
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient5 ^ 2 *
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient0)
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient0 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient5 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5 -
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient4 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6) +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 ^ 2 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional2 *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient0) := by
  constructor
  have hscaled := congrArg MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial (MazurTransfer.order49_recurrence2_exact_integer_0.identity)
  rw [toPolynomial_append_single_zero] at hscaled
  simp only [MazurTransfer.order49_recurrence3_toPolynomial_add, MazurTransfer.order49_recurrence3_toPolynomial_mul, MazurTransfer.order49_recurrence3_toPolynomial_scale, leading_polynomial, quotient_polynomial, exceptional_polynomial, input_a0, input_a6, input_b0, input_b1, input_b2, input_b3, input_b4, input_b5, input_c0] at hscaled
  exact scalar0_of_cleared_identity (C (MazurTransfer.Order49Recurrence2DenseCandidate.denominator : ℚ)) MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient0 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient0 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient4 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient5 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient0 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional2 denominator_nonzero hscaled
#print axioms solution
