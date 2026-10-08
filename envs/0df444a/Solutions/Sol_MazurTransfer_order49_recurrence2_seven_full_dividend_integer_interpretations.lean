-- Prove2me | solution 1 for MazurTransfer.order49_recurrence2_seven_full_dividend_integer_interpretations
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T12:51:48.86402+00:00
-- url     : https://prove2.me/submissions/ff676efc-01aa-4dc6-a937-5b81aed22d07

import Definitions.Def_MazurTransfer_Order49Recurrence2ReusedDenseIntegerData
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData1
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_MazurTransfer_order49_recurrence2_a0_original_chunk_interpretations
import Theorems.Thm_MazurTransfer_order49_recurrence2_a1_original_chunk_interpretations
import Theorems.Thm_MazurTransfer_order49_recurrence2_a2_original_chunk_interpretations
import Theorems.Thm_MazurTransfer_order49_recurrence2_a3_original_chunk_interpretations
import Theorems.Thm_MazurTransfer_order49_recurrence2_a4_original_chunk_interpretations
import Theorems.Thm_MazurTransfer_order49_recurrence2_a5_original_chunk_interpretations
import Theorems.Thm_MazurTransfer_order49_recurrence2_a6_original_chunk_interpretations
open Polynomial
namespace MazurTransfer.Order49Recurrence2DenseCandidate.FullTableProof
theorem toPolynomial_append (xs ys : List ℤ) : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial (xs ++ ys) = MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial xs + X ^ xs.length * MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial ys := by
  induction xs with
  | nil => simp [MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial]
  | cons x xs ih =>
    simp only [List.cons_append, MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial, ih, List.length_cons, pow_succ]
    ring
theorem toPolynomial_replicate_zero (n : ℕ) : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial (List.replicate n 0) = 0 := by
  induction n with
  | zero => simp [MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial]
  | succ n ih => simp [List.replicate_succ, MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial, ih]
private theorem a0_parts_match : MazurTransfer.Order49Recurrence2DenseCandidate.a0 = MazurTransfer.Order49Recurrence2DenseCandidate.a0Parts := by decide +kernel
private theorem a0_chunk_length_0 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk14).length = 5 := by rfl
private theorem a0_chunk_length_1 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk13).length = 8 := by rfl
private theorem a0_chunk_length_2 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk12).length = 8 := by rfl
private theorem a0_chunk_length_3 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk11).length = 8 := by rfl
private theorem a0_chunk_length_4 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk10).length = 8 := by rfl
private theorem a0_chunk_length_5 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk9).length = 8 := by rfl
private theorem a0_chunk_length_6 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk8).length = 8 := by rfl
private theorem a0_chunk_length_7 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk7).length = 8 := by rfl
private theorem a0_chunk_length_8 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk6).length = 8 := by rfl
private theorem a0_chunk_length_9 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk5).length = 8 := by rfl
private theorem a0_chunk_length_10 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk4).length = 8 := by rfl
private theorem a0_chunk_length_11 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk3).length = 8 := by rfl
private theorem a0_chunk_length_12 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk2).length = 8 := by rfl
private theorem a0_chunk_length_13 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk1).length = 8 := by rfl
private theorem a0_chunk_length_14 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk0).length = 8 := by rfl
private def a0_original_block_parts_0 : List ℤ := MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk14 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk13 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk12
private theorem a0_original_block_parts_0_length : a0_original_block_parts_0.length = 21 := by rfl
private theorem a0_original_block_parts_0_interpretation : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient0Block1 = (X : Polynomial ℚ) ^ 2 * MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial a0_original_block_parts_0 := by
  have h0 := MazurTransfer.order49_recurrence2_a0_original_chunk_interpretations.1.identity
  have h1 := MazurTransfer.order49_recurrence2_a0_original_chunk_interpretations.2.1.identity
  have h2 := MazurTransfer.order49_recurrence2_a0_original_chunk_interpretations.2.2.1.identity
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient0Block1
  rw [h0, h1, h2]
  simp only [a0_original_block_parts_0, toPolynomial_append, List.length_append, a0_chunk_length_0, a0_chunk_length_1]
  norm_num <;> ring
private def a0_original_block_parts_1 : List ℤ := MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk11 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk10 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk9 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk8 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk7 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk6 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk5 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk4 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk3 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk2 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk1 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient0Chunk0
private theorem a0_original_block_parts_1_length : a0_original_block_parts_1.length = 96 := by rfl
private theorem a0_original_block_parts_1_interpretation : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient0Block0 = (X : Polynomial ℚ) ^ 23 * MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial a0_original_block_parts_1 := by
  have h3 := MazurTransfer.order49_recurrence2_a0_original_chunk_interpretations.2.2.2.1.identity
  have h4 := MazurTransfer.order49_recurrence2_a0_original_chunk_interpretations.2.2.2.2.1.identity
  have h5 := MazurTransfer.order49_recurrence2_a0_original_chunk_interpretations.2.2.2.2.2.1.identity
  have h6 := MazurTransfer.order49_recurrence2_a0_original_chunk_interpretations.2.2.2.2.2.2.1.identity
  have h7 := MazurTransfer.order49_recurrence2_a0_original_chunk_interpretations.2.2.2.2.2.2.2.1.identity
  have h8 := MazurTransfer.order49_recurrence2_a0_original_chunk_interpretations.2.2.2.2.2.2.2.2.1.identity
  have h9 := MazurTransfer.order49_recurrence2_a0_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.1.identity
  have h10 := MazurTransfer.order49_recurrence2_a0_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.1.identity
  have h11 := MazurTransfer.order49_recurrence2_a0_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h12 := MazurTransfer.order49_recurrence2_a0_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h13 := MazurTransfer.order49_recurrence2_a0_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h14 := MazurTransfer.order49_recurrence2_a0_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.identity
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient0Block0
  rw [h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
  simp only [a0_original_block_parts_1, toPolynomial_append, List.length_append, a0_chunk_length_3, a0_chunk_length_4, a0_chunk_length_5, a0_chunk_length_6, a0_chunk_length_7, a0_chunk_length_8, a0_chunk_length_9, a0_chunk_length_10, a0_chunk_length_11, a0_chunk_length_12, a0_chunk_length_13]
  norm_num <;> ring
theorem a0_full_interpretation : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.a0 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient0 := by
  have parts : MazurTransfer.Order49Recurrence2DenseCandidate.a0Parts = List.replicate 2 0 ++ (a0_original_block_parts_0 ++ a0_original_block_parts_1) := by decide +kernel
  rw [a0_parts_match, parts, toPolynomial_append, toPolynomial_append]
  simp only [toPolynomial_replicate_zero, List.length_replicate, a0_original_block_parts_0_length, zero_add]
  have combine (P Q : Polynomial ℚ) : (X : Polynomial ℚ) ^ 2 * (P + X ^ 21 * Q) = X ^ 2 * P + X ^ 23 * Q := by ring
  rw [combine, ← a0_original_block_parts_0_interpretation, ← a0_original_block_parts_1_interpretation]
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient0
  exact add_comm _ _
private theorem a1_parts_match : MazurTransfer.Order49Recurrence2DenseCandidate.a1 = MazurTransfer.Order49Recurrence2DenseCandidate.a1Parts := by decide +kernel
private theorem a1_chunk_length_0 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk14).length = 1 := by rfl
private theorem a1_chunk_length_1 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk13).length = 8 := by rfl
private theorem a1_chunk_length_2 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk12).length = 8 := by rfl
private theorem a1_chunk_length_3 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk11).length = 8 := by rfl
private theorem a1_chunk_length_4 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk10).length = 8 := by rfl
private theorem a1_chunk_length_5 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk9).length = 8 := by rfl
private theorem a1_chunk_length_6 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk8).length = 8 := by rfl
private theorem a1_chunk_length_7 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk7).length = 8 := by rfl
private theorem a1_chunk_length_8 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk6).length = 8 := by rfl
private theorem a1_chunk_length_9 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk5).length = 8 := by rfl
private theorem a1_chunk_length_10 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk4).length = 8 := by rfl
private theorem a1_chunk_length_11 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk3).length = 8 := by rfl
private theorem a1_chunk_length_12 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk2).length = 8 := by rfl
private theorem a1_chunk_length_13 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk1).length = 8 := by rfl
private theorem a1_chunk_length_14 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk0).length = 8 := by rfl
private def a1_original_block_parts_0 : List ℤ := MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk14 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk13 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk12
private theorem a1_original_block_parts_0_length : a1_original_block_parts_0.length = 17 := by rfl
private theorem a1_original_block_parts_0_interpretation : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient1Block1 = (X : Polynomial ℚ) ^ 2 * MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial a1_original_block_parts_0 := by
  have h0 := MazurTransfer.order49_recurrence2_a1_original_chunk_interpretations.1.identity
  have h1 := MazurTransfer.order49_recurrence2_a1_original_chunk_interpretations.2.1.identity
  have h2 := MazurTransfer.order49_recurrence2_a1_original_chunk_interpretations.2.2.1.identity
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient1Block1
  rw [h0, h1, h2]
  simp only [a1_original_block_parts_0, toPolynomial_append, List.length_append, a1_chunk_length_0, a1_chunk_length_1]
  norm_num <;> ring
private def a1_original_block_parts_1 : List ℤ := MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk11 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk10 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk9 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk8 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk7 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk6 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk5 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk4 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk3 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk2 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk1 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient1Chunk0
private theorem a1_original_block_parts_1_length : a1_original_block_parts_1.length = 96 := by rfl
private theorem a1_original_block_parts_1_interpretation : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient1Block0 = (X : Polynomial ℚ) ^ 19 * MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial a1_original_block_parts_1 := by
  have h3 := MazurTransfer.order49_recurrence2_a1_original_chunk_interpretations.2.2.2.1.identity
  have h4 := MazurTransfer.order49_recurrence2_a1_original_chunk_interpretations.2.2.2.2.1.identity
  have h5 := MazurTransfer.order49_recurrence2_a1_original_chunk_interpretations.2.2.2.2.2.1.identity
  have h6 := MazurTransfer.order49_recurrence2_a1_original_chunk_interpretations.2.2.2.2.2.2.1.identity
  have h7 := MazurTransfer.order49_recurrence2_a1_original_chunk_interpretations.2.2.2.2.2.2.2.1.identity
  have h8 := MazurTransfer.order49_recurrence2_a1_original_chunk_interpretations.2.2.2.2.2.2.2.2.1.identity
  have h9 := MazurTransfer.order49_recurrence2_a1_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.1.identity
  have h10 := MazurTransfer.order49_recurrence2_a1_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.1.identity
  have h11 := MazurTransfer.order49_recurrence2_a1_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h12 := MazurTransfer.order49_recurrence2_a1_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h13 := MazurTransfer.order49_recurrence2_a1_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h14 := MazurTransfer.order49_recurrence2_a1_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.identity
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient1Block0
  rw [h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
  simp only [a1_original_block_parts_1, toPolynomial_append, List.length_append, a1_chunk_length_3, a1_chunk_length_4, a1_chunk_length_5, a1_chunk_length_6, a1_chunk_length_7, a1_chunk_length_8, a1_chunk_length_9, a1_chunk_length_10, a1_chunk_length_11, a1_chunk_length_12, a1_chunk_length_13]
  norm_num <;> ring
theorem a1_full_interpretation : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.a1 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient1 := by
  have parts : MazurTransfer.Order49Recurrence2DenseCandidate.a1Parts = List.replicate 2 0 ++ (a1_original_block_parts_0 ++ a1_original_block_parts_1) := by decide +kernel
  rw [a1_parts_match, parts, toPolynomial_append, toPolynomial_append]
  simp only [toPolynomial_replicate_zero, List.length_replicate, a1_original_block_parts_0_length, zero_add]
  have combine (P Q : Polynomial ℚ) : (X : Polynomial ℚ) ^ 2 * (P + X ^ 17 * Q) = X ^ 2 * P + X ^ 19 * Q := by ring
  rw [combine, ← a1_original_block_parts_0_interpretation, ← a1_original_block_parts_1_interpretation]
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient1
  exact add_comm _ _
private theorem a2_parts_match : MazurTransfer.Order49Recurrence2DenseCandidate.a2 = MazurTransfer.Order49Recurrence2DenseCandidate.a2Parts := by decide +kernel
private theorem a2_chunk_length_0 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient2Chunk13).length = 5 := by rfl
private theorem a2_chunk_length_1 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient2Chunk12).length = 8 := by rfl
private theorem a2_chunk_length_2 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient2Chunk11).length = 8 := by rfl
private theorem a2_chunk_length_3 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient2Chunk10).length = 8 := by rfl
private theorem a2_chunk_length_4 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient2Chunk9).length = 8 := by rfl
private theorem a2_chunk_length_5 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient2Chunk8).length = 8 := by rfl
private theorem a2_chunk_length_6 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient2Chunk7).length = 8 := by rfl
private theorem a2_chunk_length_7 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient2Chunk6).length = 8 := by rfl
private theorem a2_chunk_length_8 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient2Chunk5).length = 8 := by rfl
private theorem a2_chunk_length_9 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient2Chunk4).length = 8 := by rfl
private theorem a2_chunk_length_10 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient2Chunk3).length = 8 := by rfl
private theorem a2_chunk_length_11 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient2Chunk2).length = 8 := by rfl
private theorem a2_chunk_length_12 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient2Chunk1).length = 8 := by rfl
private theorem a2_chunk_length_13 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient2Chunk0).length = 8 := by rfl
private def a2_original_block_parts_0 : List ℤ := MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient2Chunk13 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient2Chunk12
private theorem a2_original_block_parts_0_length : a2_original_block_parts_0.length = 13 := by rfl
private theorem a2_original_block_parts_0_interpretation : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient2Block1 = (X : Polynomial ℚ) ^ 2 * MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial a2_original_block_parts_0 := by
  have h0 := MazurTransfer.order49_recurrence2_a2_original_chunk_interpretations.1.identity
  have h1 := MazurTransfer.order49_recurrence2_a2_original_chunk_interpretations.2.1.identity
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient2Block1
  rw [h0, h1]
  simp only [a2_original_block_parts_0, toPolynomial_append, List.length_append, a2_chunk_length_0]
  norm_num <;> ring
private def a2_original_block_parts_1 : List ℤ := MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient2Chunk11 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient2Chunk10 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient2Chunk9 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient2Chunk8 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient2Chunk7 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient2Chunk6 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient2Chunk5 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient2Chunk4 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient2Chunk3 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient2Chunk2 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient2Chunk1 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient2Chunk0
private theorem a2_original_block_parts_1_length : a2_original_block_parts_1.length = 96 := by rfl
private theorem a2_original_block_parts_1_interpretation : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient2Block0 = (X : Polynomial ℚ) ^ 15 * MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial a2_original_block_parts_1 := by
  have h2 := MazurTransfer.order49_recurrence2_a2_original_chunk_interpretations.2.2.1.identity
  have h3 := MazurTransfer.order49_recurrence2_a2_original_chunk_interpretations.2.2.2.1.identity
  have h4 := MazurTransfer.order49_recurrence2_a2_original_chunk_interpretations.2.2.2.2.1.identity
  have h5 := MazurTransfer.order49_recurrence2_a2_original_chunk_interpretations.2.2.2.2.2.1.identity
  have h6 := MazurTransfer.order49_recurrence2_a2_original_chunk_interpretations.2.2.2.2.2.2.1.identity
  have h7 := MazurTransfer.order49_recurrence2_a2_original_chunk_interpretations.2.2.2.2.2.2.2.1.identity
  have h8 := MazurTransfer.order49_recurrence2_a2_original_chunk_interpretations.2.2.2.2.2.2.2.2.1.identity
  have h9 := MazurTransfer.order49_recurrence2_a2_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.1.identity
  have h10 := MazurTransfer.order49_recurrence2_a2_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.1.identity
  have h11 := MazurTransfer.order49_recurrence2_a2_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h12 := MazurTransfer.order49_recurrence2_a2_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h13 := MazurTransfer.order49_recurrence2_a2_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.2.identity
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient2Block0
  rw [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  simp only [a2_original_block_parts_1, toPolynomial_append, List.length_append, a2_chunk_length_2, a2_chunk_length_3, a2_chunk_length_4, a2_chunk_length_5, a2_chunk_length_6, a2_chunk_length_7, a2_chunk_length_8, a2_chunk_length_9, a2_chunk_length_10, a2_chunk_length_11, a2_chunk_length_12]
  norm_num <;> ring
theorem a2_full_interpretation : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.a2 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient2 := by
  have parts : MazurTransfer.Order49Recurrence2DenseCandidate.a2Parts = List.replicate 2 0 ++ (a2_original_block_parts_0 ++ a2_original_block_parts_1) := by decide +kernel
  rw [a2_parts_match, parts, toPolynomial_append, toPolynomial_append]
  simp only [toPolynomial_replicate_zero, List.length_replicate, a2_original_block_parts_0_length, zero_add]
  have combine (P Q : Polynomial ℚ) : (X : Polynomial ℚ) ^ 2 * (P + X ^ 13 * Q) = X ^ 2 * P + X ^ 15 * Q := by ring
  rw [combine, ← a2_original_block_parts_0_interpretation, ← a2_original_block_parts_1_interpretation]
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient2
  exact add_comm _ _
private theorem a3_parts_match : MazurTransfer.Order49Recurrence2DenseCandidate.a3 = MazurTransfer.Order49Recurrence2DenseCandidate.a3Parts := by decide +kernel
private theorem a3_chunk_length_0 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient3Chunk13).length = 2 := by rfl
private theorem a3_chunk_length_1 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient3Chunk12).length = 8 := by rfl
private theorem a3_chunk_length_2 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient3Chunk11).length = 8 := by rfl
private theorem a3_chunk_length_3 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient3Chunk10).length = 8 := by rfl
private theorem a3_chunk_length_4 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient3Chunk9).length = 8 := by rfl
private theorem a3_chunk_length_5 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient3Chunk8).length = 8 := by rfl
private theorem a3_chunk_length_6 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient3Chunk7).length = 8 := by rfl
private theorem a3_chunk_length_7 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient3Chunk6).length = 8 := by rfl
private theorem a3_chunk_length_8 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient3Chunk5).length = 8 := by rfl
private theorem a3_chunk_length_9 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient3Chunk4).length = 8 := by rfl
private theorem a3_chunk_length_10 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient3Chunk3).length = 8 := by rfl
private theorem a3_chunk_length_11 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient3Chunk2).length = 8 := by rfl
private theorem a3_chunk_length_12 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient3Chunk1).length = 8 := by rfl
private theorem a3_chunk_length_13 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient3Chunk0).length = 8 := by rfl
private def a3_original_block_parts_0 : List ℤ := MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient3Chunk13 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient3Chunk12
private theorem a3_original_block_parts_0_length : a3_original_block_parts_0.length = 10 := by rfl
private theorem a3_original_block_parts_0_interpretation : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient3Block1 = (X : Polynomial ℚ) ^ 1 * MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial a3_original_block_parts_0 := by
  have h0 := MazurTransfer.order49_recurrence2_a3_original_chunk_interpretations.1.identity
  have h1 := MazurTransfer.order49_recurrence2_a3_original_chunk_interpretations.2.1.identity
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient3Block1
  rw [h0, h1]
  simp only [a3_original_block_parts_0, toPolynomial_append, List.length_append, a3_chunk_length_0]
  norm_num <;> ring
private def a3_original_block_parts_1 : List ℤ := MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient3Chunk11 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient3Chunk10 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient3Chunk9 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient3Chunk8 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient3Chunk7 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient3Chunk6 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient3Chunk5 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient3Chunk4 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient3Chunk3 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient3Chunk2 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient3Chunk1 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient3Chunk0
private theorem a3_original_block_parts_1_length : a3_original_block_parts_1.length = 96 := by rfl
private theorem a3_original_block_parts_1_interpretation : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient3Block0 = (X : Polynomial ℚ) ^ 11 * MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial a3_original_block_parts_1 := by
  have h2 := MazurTransfer.order49_recurrence2_a3_original_chunk_interpretations.2.2.1.identity
  have h3 := MazurTransfer.order49_recurrence2_a3_original_chunk_interpretations.2.2.2.1.identity
  have h4 := MazurTransfer.order49_recurrence2_a3_original_chunk_interpretations.2.2.2.2.1.identity
  have h5 := MazurTransfer.order49_recurrence2_a3_original_chunk_interpretations.2.2.2.2.2.1.identity
  have h6 := MazurTransfer.order49_recurrence2_a3_original_chunk_interpretations.2.2.2.2.2.2.1.identity
  have h7 := MazurTransfer.order49_recurrence2_a3_original_chunk_interpretations.2.2.2.2.2.2.2.1.identity
  have h8 := MazurTransfer.order49_recurrence2_a3_original_chunk_interpretations.2.2.2.2.2.2.2.2.1.identity
  have h9 := MazurTransfer.order49_recurrence2_a3_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.1.identity
  have h10 := MazurTransfer.order49_recurrence2_a3_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.1.identity
  have h11 := MazurTransfer.order49_recurrence2_a3_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h12 := MazurTransfer.order49_recurrence2_a3_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h13 := MazurTransfer.order49_recurrence2_a3_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.2.identity
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient3Block0
  rw [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  simp only [a3_original_block_parts_1, toPolynomial_append, List.length_append, a3_chunk_length_2, a3_chunk_length_3, a3_chunk_length_4, a3_chunk_length_5, a3_chunk_length_6, a3_chunk_length_7, a3_chunk_length_8, a3_chunk_length_9, a3_chunk_length_10, a3_chunk_length_11, a3_chunk_length_12]
  norm_num <;> ring
theorem a3_full_interpretation : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.a3 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient3 := by
  have parts : MazurTransfer.Order49Recurrence2DenseCandidate.a3Parts = List.replicate 1 0 ++ (a3_original_block_parts_0 ++ a3_original_block_parts_1) := by decide +kernel
  rw [a3_parts_match, parts, toPolynomial_append, toPolynomial_append]
  simp only [toPolynomial_replicate_zero, List.length_replicate, a3_original_block_parts_0_length, zero_add]
  have combine (P Q : Polynomial ℚ) : (X : Polynomial ℚ) ^ 1 * (P + X ^ 10 * Q) = X ^ 1 * P + X ^ 11 * Q := by ring
  rw [combine, ← a3_original_block_parts_0_interpretation, ← a3_original_block_parts_1_interpretation]
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient3
  exact add_comm _ _
private theorem a4_parts_match : MazurTransfer.Order49Recurrence2DenseCandidate.a4 = MazurTransfer.Order49Recurrence2DenseCandidate.a4Parts := by decide +kernel
private theorem a4_chunk_length_0 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient4Chunk12).length = 6 := by rfl
private theorem a4_chunk_length_1 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient4Chunk11).length = 8 := by rfl
private theorem a4_chunk_length_2 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient4Chunk10).length = 8 := by rfl
private theorem a4_chunk_length_3 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient4Chunk9).length = 8 := by rfl
private theorem a4_chunk_length_4 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient4Chunk8).length = 8 := by rfl
private theorem a4_chunk_length_5 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient4Chunk7).length = 8 := by rfl
private theorem a4_chunk_length_6 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient4Chunk6).length = 8 := by rfl
private theorem a4_chunk_length_7 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient4Chunk5).length = 8 := by rfl
private theorem a4_chunk_length_8 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient4Chunk4).length = 8 := by rfl
private theorem a4_chunk_length_9 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient4Chunk3).length = 8 := by rfl
private theorem a4_chunk_length_10 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient4Chunk2).length = 8 := by rfl
private theorem a4_chunk_length_11 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient4Chunk1).length = 8 := by rfl
private theorem a4_chunk_length_12 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient4Chunk0).length = 8 := by rfl
private def a4_original_block_parts_0 : List ℤ := MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient4Chunk12
private theorem a4_original_block_parts_0_length : a4_original_block_parts_0.length = 6 := by rfl
private theorem a4_original_block_parts_0_interpretation : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient4Block1 = (X : Polynomial ℚ) ^ 1 * MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial a4_original_block_parts_0 := by
  have h0 := MazurTransfer.order49_recurrence2_a4_original_chunk_interpretations.1.identity
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient4Block1
  rw [h0]
  simp only [a4_original_block_parts_0]
private def a4_original_block_parts_1 : List ℤ := MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient4Chunk11 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient4Chunk10 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient4Chunk9 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient4Chunk8 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient4Chunk7 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient4Chunk6 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient4Chunk5 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient4Chunk4 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient4Chunk3 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient4Chunk2 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient4Chunk1 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient4Chunk0
private theorem a4_original_block_parts_1_length : a4_original_block_parts_1.length = 96 := by rfl
private theorem a4_original_block_parts_1_interpretation : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient4Block0 = (X : Polynomial ℚ) ^ 7 * MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial a4_original_block_parts_1 := by
  have h1 := MazurTransfer.order49_recurrence2_a4_original_chunk_interpretations.2.1.identity
  have h2 := MazurTransfer.order49_recurrence2_a4_original_chunk_interpretations.2.2.1.identity
  have h3 := MazurTransfer.order49_recurrence2_a4_original_chunk_interpretations.2.2.2.1.identity
  have h4 := MazurTransfer.order49_recurrence2_a4_original_chunk_interpretations.2.2.2.2.1.identity
  have h5 := MazurTransfer.order49_recurrence2_a4_original_chunk_interpretations.2.2.2.2.2.1.identity
  have h6 := MazurTransfer.order49_recurrence2_a4_original_chunk_interpretations.2.2.2.2.2.2.1.identity
  have h7 := MazurTransfer.order49_recurrence2_a4_original_chunk_interpretations.2.2.2.2.2.2.2.1.identity
  have h8 := MazurTransfer.order49_recurrence2_a4_original_chunk_interpretations.2.2.2.2.2.2.2.2.1.identity
  have h9 := MazurTransfer.order49_recurrence2_a4_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.1.identity
  have h10 := MazurTransfer.order49_recurrence2_a4_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.1.identity
  have h11 := MazurTransfer.order49_recurrence2_a4_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h12 := MazurTransfer.order49_recurrence2_a4_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.identity
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient4Block0
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  simp only [a4_original_block_parts_1, toPolynomial_append, List.length_append, a4_chunk_length_1, a4_chunk_length_2, a4_chunk_length_3, a4_chunk_length_4, a4_chunk_length_5, a4_chunk_length_6, a4_chunk_length_7, a4_chunk_length_8, a4_chunk_length_9, a4_chunk_length_10, a4_chunk_length_11]
  norm_num <;> ring
theorem a4_full_interpretation : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.a4 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient4 := by
  have parts : MazurTransfer.Order49Recurrence2DenseCandidate.a4Parts = List.replicate 1 0 ++ (a4_original_block_parts_0 ++ a4_original_block_parts_1) := by decide +kernel
  rw [a4_parts_match, parts, toPolynomial_append, toPolynomial_append]
  simp only [toPolynomial_replicate_zero, List.length_replicate, a4_original_block_parts_0_length, zero_add]
  have combine (P Q : Polynomial ℚ) : (X : Polynomial ℚ) ^ 1 * (P + X ^ 6 * Q) = X ^ 1 * P + X ^ 7 * Q := by ring
  rw [combine, ← a4_original_block_parts_0_interpretation, ← a4_original_block_parts_1_interpretation]
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient4
  exact add_comm _ _
private theorem a5_parts_match : MazurTransfer.Order49Recurrence2DenseCandidate.a5 = MazurTransfer.Order49Recurrence2DenseCandidate.a5Parts := by decide +kernel
private theorem a5_chunk_length_0 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient5Chunk12).length = 3 := by rfl
private theorem a5_chunk_length_1 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient5Chunk11).length = 8 := by rfl
private theorem a5_chunk_length_2 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient5Chunk10).length = 8 := by rfl
private theorem a5_chunk_length_3 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient5Chunk9).length = 8 := by rfl
private theorem a5_chunk_length_4 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient5Chunk8).length = 8 := by rfl
private theorem a5_chunk_length_5 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient5Chunk7).length = 8 := by rfl
private theorem a5_chunk_length_6 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient5Chunk6).length = 8 := by rfl
private theorem a5_chunk_length_7 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient5Chunk5).length = 8 := by rfl
private theorem a5_chunk_length_8 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient5Chunk4).length = 8 := by rfl
private theorem a5_chunk_length_9 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient5Chunk3).length = 8 := by rfl
private theorem a5_chunk_length_10 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient5Chunk2).length = 8 := by rfl
private theorem a5_chunk_length_11 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient5Chunk1).length = 8 := by rfl
private theorem a5_chunk_length_12 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient5Chunk0).length = 8 := by rfl
private def a5_original_block_parts_0 : List ℤ := MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient5Chunk12
private theorem a5_original_block_parts_0_length : a5_original_block_parts_0.length = 3 := by rfl
private theorem a5_original_block_parts_0_interpretation : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5Block1 = (X : Polynomial ℚ) ^ 0 * MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial a5_original_block_parts_0 := by
  have h0 := MazurTransfer.order49_recurrence2_a5_original_chunk_interpretations.1.identity
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5Block1
  rw [h0]
  simp only [a5_original_block_parts_0]
private def a5_original_block_parts_1 : List ℤ := MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient5Chunk11 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient5Chunk10 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient5Chunk9 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient5Chunk8 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient5Chunk7 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient5Chunk6 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient5Chunk5 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient5Chunk4 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient5Chunk3 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient5Chunk2 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient5Chunk1 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient5Chunk0
private theorem a5_original_block_parts_1_length : a5_original_block_parts_1.length = 96 := by rfl
private theorem a5_original_block_parts_1_interpretation : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5Block0 = (X : Polynomial ℚ) ^ 3 * MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial a5_original_block_parts_1 := by
  have h1 := MazurTransfer.order49_recurrence2_a5_original_chunk_interpretations.2.1.identity
  have h2 := MazurTransfer.order49_recurrence2_a5_original_chunk_interpretations.2.2.1.identity
  have h3 := MazurTransfer.order49_recurrence2_a5_original_chunk_interpretations.2.2.2.1.identity
  have h4 := MazurTransfer.order49_recurrence2_a5_original_chunk_interpretations.2.2.2.2.1.identity
  have h5 := MazurTransfer.order49_recurrence2_a5_original_chunk_interpretations.2.2.2.2.2.1.identity
  have h6 := MazurTransfer.order49_recurrence2_a5_original_chunk_interpretations.2.2.2.2.2.2.1.identity
  have h7 := MazurTransfer.order49_recurrence2_a5_original_chunk_interpretations.2.2.2.2.2.2.2.1.identity
  have h8 := MazurTransfer.order49_recurrence2_a5_original_chunk_interpretations.2.2.2.2.2.2.2.2.1.identity
  have h9 := MazurTransfer.order49_recurrence2_a5_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.1.identity
  have h10 := MazurTransfer.order49_recurrence2_a5_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.1.identity
  have h11 := MazurTransfer.order49_recurrence2_a5_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h12 := MazurTransfer.order49_recurrence2_a5_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.identity
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5Block0
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  simp only [a5_original_block_parts_1, toPolynomial_append, List.length_append, a5_chunk_length_1, a5_chunk_length_2, a5_chunk_length_3, a5_chunk_length_4, a5_chunk_length_5, a5_chunk_length_6, a5_chunk_length_7, a5_chunk_length_8, a5_chunk_length_9, a5_chunk_length_10, a5_chunk_length_11]
  norm_num <;> ring
theorem a5_full_interpretation : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.a5 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5 := by
  have parts : MazurTransfer.Order49Recurrence2DenseCandidate.a5Parts = List.replicate 0 0 ++ (a5_original_block_parts_0 ++ a5_original_block_parts_1) := by decide +kernel
  rw [a5_parts_match, parts, toPolynomial_append, toPolynomial_append]
  simp only [toPolynomial_replicate_zero, List.length_replicate, a5_original_block_parts_0_length, zero_add]
  have combine (P Q : Polynomial ℚ) : (X : Polynomial ℚ) ^ 0 * (P + X ^ 3 * Q) = X ^ 0 * P + X ^ 3 * Q := by ring
  rw [combine, ← a5_original_block_parts_0_interpretation, ← a5_original_block_parts_1_interpretation]
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5
  exact add_comm _ _
private theorem a6_parts_match : MazurTransfer.Order49Recurrence2DenseCandidate.a6 = MazurTransfer.Order49Recurrence2DenseCandidate.a6Parts := by decide +kernel
private theorem a6_chunk_length_0 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient6Chunk11).length = 8 := by rfl
private theorem a6_chunk_length_1 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient6Chunk10).length = 8 := by rfl
private theorem a6_chunk_length_2 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient6Chunk9).length = 8 := by rfl
private theorem a6_chunk_length_3 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient6Chunk8).length = 8 := by rfl
private theorem a6_chunk_length_4 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient6Chunk7).length = 8 := by rfl
private theorem a6_chunk_length_5 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient6Chunk6).length = 8 := by rfl
private theorem a6_chunk_length_6 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient6Chunk5).length = 8 := by rfl
private theorem a6_chunk_length_7 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient6Chunk4).length = 8 := by rfl
private theorem a6_chunk_length_8 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient6Chunk3).length = 8 := by rfl
private theorem a6_chunk_length_9 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient6Chunk2).length = 8 := by rfl
private theorem a6_chunk_length_10 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient6Chunk1).length = 8 := by rfl
private theorem a6_chunk_length_11 : (MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient6Chunk0).length = 8 := by rfl
private def a6_original_block_parts_0 : List ℤ := MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient6Chunk11 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient6Chunk10 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient6Chunk9 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient6Chunk8 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient6Chunk7 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient6Chunk6 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient6Chunk5 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient6Chunk4 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient6Chunk3 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient6Chunk2 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient6Chunk1 ++ MazurTransfer.Order49Recurrence2DenseCandidate.chunk_remainder2Coefficient6Chunk0
private theorem a6_original_block_parts_0_length : a6_original_block_parts_0.length = 96 := by rfl
private theorem a6_original_block_parts_0_interpretation : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6Block0 = (X : Polynomial ℚ) ^ 0 * MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial a6_original_block_parts_0 := by
  have h0 := MazurTransfer.order49_recurrence2_a6_original_chunk_interpretations.1.identity
  have h1 := MazurTransfer.order49_recurrence2_a6_original_chunk_interpretations.2.1.identity
  have h2 := MazurTransfer.order49_recurrence2_a6_original_chunk_interpretations.2.2.1.identity
  have h3 := MazurTransfer.order49_recurrence2_a6_original_chunk_interpretations.2.2.2.1.identity
  have h4 := MazurTransfer.order49_recurrence2_a6_original_chunk_interpretations.2.2.2.2.1.identity
  have h5 := MazurTransfer.order49_recurrence2_a6_original_chunk_interpretations.2.2.2.2.2.1.identity
  have h6 := MazurTransfer.order49_recurrence2_a6_original_chunk_interpretations.2.2.2.2.2.2.1.identity
  have h7 := MazurTransfer.order49_recurrence2_a6_original_chunk_interpretations.2.2.2.2.2.2.2.1.identity
  have h8 := MazurTransfer.order49_recurrence2_a6_original_chunk_interpretations.2.2.2.2.2.2.2.2.1.identity
  have h9 := MazurTransfer.order49_recurrence2_a6_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.1.identity
  have h10 := MazurTransfer.order49_recurrence2_a6_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.1.identity
  have h11 := MazurTransfer.order49_recurrence2_a6_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.identity
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6Block0
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  simp only [a6_original_block_parts_0, toPolynomial_append, List.length_append, a6_chunk_length_0, a6_chunk_length_1, a6_chunk_length_2, a6_chunk_length_3, a6_chunk_length_4, a6_chunk_length_5, a6_chunk_length_6, a6_chunk_length_7, a6_chunk_length_8, a6_chunk_length_9, a6_chunk_length_10]
  norm_num <;> ring
theorem a6_full_interpretation : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.a6 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 := by
  have parts : MazurTransfer.Order49Recurrence2DenseCandidate.a6Parts = a6_original_block_parts_0 := by decide +kernel
  rw [a6_parts_match, parts]
  have h := a6_original_block_parts_0_interpretation
  simp only [pow_zero, one_mul] at h
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6
  exact h.symm
end MazurTransfer.Order49Recurrence2DenseCandidate.FullTableProof
theorem solution : MazurTransfer.ExactEqualityCertificate (α := Polynomial ℚ) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.a0) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient0) ∧
    MazurTransfer.ExactEqualityCertificate (α := Polynomial ℚ) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.a1) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient1) ∧
    MazurTransfer.ExactEqualityCertificate (α := Polynomial ℚ) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.a2) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient2) ∧
    MazurTransfer.ExactEqualityCertificate (α := Polynomial ℚ) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.a3) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient3) ∧
    MazurTransfer.ExactEqualityCertificate (α := Polynomial ℚ) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.a4) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient4) ∧
    MazurTransfer.ExactEqualityCertificate (α := Polynomial ℚ) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.a5) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5) ∧
    MazurTransfer.ExactEqualityCertificate (α := Polynomial ℚ) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence2DenseCandidate.a6) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6) := by
  exact ⟨⟨MazurTransfer.Order49Recurrence2DenseCandidate.FullTableProof.a0_full_interpretation⟩, ⟨⟨MazurTransfer.Order49Recurrence2DenseCandidate.FullTableProof.a1_full_interpretation⟩, ⟨⟨MazurTransfer.Order49Recurrence2DenseCandidate.FullTableProof.a2_full_interpretation⟩, ⟨⟨MazurTransfer.Order49Recurrence2DenseCandidate.FullTableProof.a3_full_interpretation⟩, ⟨⟨MazurTransfer.Order49Recurrence2DenseCandidate.FullTableProof.a4_full_interpretation⟩, ⟨⟨MazurTransfer.Order49Recurrence2DenseCandidate.FullTableProof.a5_full_interpretation⟩, ⟨MazurTransfer.Order49Recurrence2DenseCandidate.FullTableProof.a6_full_interpretation⟩⟩⟩⟩⟩⟩⟩
#print axioms solution
