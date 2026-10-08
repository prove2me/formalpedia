-- Prove2me | solution 1 for MazurTransfer.order49_recurrence5_five_full_integer_table_interpretations
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T11:19:39.733965+00:00
-- url     : https://prove2.me/submissions/3fcb8d80-a8a4-4b69-bc93-0e1798d5a9b0

import Definitions.Def_MazurTransfer_Order49Recurrence5DenseIntegerChunkDataPart1
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData5
import Definitions.Def_MazurTransfer_Order49Recurrence3StandaloneDenseData3
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_MazurTransfer_order49_recurrence5_b0_original_chunk_interpretations
import Theorems.Thm_MazurTransfer_order49_recurrence5_b1_original_chunk_interpretations
import Theorems.Thm_MazurTransfer_order49_recurrence5_b2_original_chunk_interpretations
import Theorems.Thm_MazurTransfer_order49_recurrence5_c0_original_chunk_interpretations
import Theorems.Thm_MazurTransfer_order49_recurrence5_c1_original_chunk_interpretations
open Polynomial
namespace MazurTransfer.Order49Recurrence5DenseCandidate.FullTableProof
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
private theorem b0_parts_match : MazurTransfer.Order49Recurrence5DenseCandidate.b0 = MazurTransfer.Order49Recurrence5DenseCandidate.b0Parts := by decide +kernel
private theorem b0_chunk_length_0 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk19).length = 1 := by rfl
private theorem b0_chunk_length_1 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk18).length = 8 := by rfl
private theorem b0_chunk_length_2 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk17).length = 8 := by rfl
private theorem b0_chunk_length_3 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk16).length = 8 := by rfl
private theorem b0_chunk_length_4 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk15).length = 8 := by rfl
private theorem b0_chunk_length_5 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk14).length = 8 := by rfl
private theorem b0_chunk_length_6 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk13).length = 8 := by rfl
private theorem b0_chunk_length_7 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk12).length = 8 := by rfl
private theorem b0_chunk_length_8 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk11).length = 8 := by rfl
private theorem b0_chunk_length_9 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk10).length = 8 := by rfl
private theorem b0_chunk_length_10 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk9).length = 8 := by rfl
private theorem b0_chunk_length_11 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk8).length = 8 := by rfl
private theorem b0_chunk_length_12 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk7).length = 8 := by rfl
private theorem b0_chunk_length_13 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk6).length = 8 := by rfl
private theorem b0_chunk_length_14 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk5).length = 8 := by rfl
private theorem b0_chunk_length_15 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk4).length = 8 := by rfl
private theorem b0_chunk_length_16 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk3).length = 8 := by rfl
private theorem b0_chunk_length_17 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk2).length = 8 := by rfl
private theorem b0_chunk_length_18 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk1).length = 8 := by rfl
private theorem b0_chunk_length_19 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk0).length = 8 := by rfl
private def b0_original_block_parts_0 : List ℤ := MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk19 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk18 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk17 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk16 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk15 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk14 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk13 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk12
private theorem b0_original_block_parts_0_length : b0_original_block_parts_0.length = 57 := by rfl
private theorem b0_original_block_parts_0_interpretation : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0Block1 = (X : Polynomial ℚ) ^ 1 * MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial b0_original_block_parts_0 := by
  have h0 := MazurTransfer.order49_recurrence5_b0_original_chunk_interpretations.1.identity
  have h1 := MazurTransfer.order49_recurrence5_b0_original_chunk_interpretations.2.1.identity
  have h2 := MazurTransfer.order49_recurrence5_b0_original_chunk_interpretations.2.2.1.identity
  have h3 := MazurTransfer.order49_recurrence5_b0_original_chunk_interpretations.2.2.2.1.identity
  have h4 := MazurTransfer.order49_recurrence5_b0_original_chunk_interpretations.2.2.2.2.1.identity
  have h5 := MazurTransfer.order49_recurrence5_b0_original_chunk_interpretations.2.2.2.2.2.1.identity
  have h6 := MazurTransfer.order49_recurrence5_b0_original_chunk_interpretations.2.2.2.2.2.2.1.identity
  have h7 := MazurTransfer.order49_recurrence5_b0_original_chunk_interpretations.2.2.2.2.2.2.2.1.identity
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0Block1
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  simp only [b0_original_block_parts_0, toPolynomial_append, List.length_append, b0_chunk_length_0, b0_chunk_length_1, b0_chunk_length_2, b0_chunk_length_3, b0_chunk_length_4, b0_chunk_length_5, b0_chunk_length_6]
  norm_num <;> ring
private def b0_original_block_parts_1 : List ℤ := MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk11 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk10 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk9 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk8 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk7 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk6 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk5 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk4 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk3 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk2 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk1 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient0Chunk0
private theorem b0_original_block_parts_1_length : b0_original_block_parts_1.length = 96 := by rfl
private theorem b0_original_block_parts_1_interpretation : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0Block0 = (X : Polynomial ℚ) ^ 58 * MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial b0_original_block_parts_1 := by
  have h8 := MazurTransfer.order49_recurrence5_b0_original_chunk_interpretations.2.2.2.2.2.2.2.2.1.identity
  have h9 := MazurTransfer.order49_recurrence5_b0_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.1.identity
  have h10 := MazurTransfer.order49_recurrence5_b0_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.1.identity
  have h11 := MazurTransfer.order49_recurrence5_b0_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h12 := MazurTransfer.order49_recurrence5_b0_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h13 := MazurTransfer.order49_recurrence5_b0_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h14 := MazurTransfer.order49_recurrence5_b0_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h15 := MazurTransfer.order49_recurrence5_b0_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h16 := MazurTransfer.order49_recurrence5_b0_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h17 := MazurTransfer.order49_recurrence5_b0_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h18 := MazurTransfer.order49_recurrence5_b0_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h19 := MazurTransfer.order49_recurrence5_b0_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.identity
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0Block0
  rw [h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]
  simp only [b0_original_block_parts_1, toPolynomial_append, List.length_append, b0_chunk_length_8, b0_chunk_length_9, b0_chunk_length_10, b0_chunk_length_11, b0_chunk_length_12, b0_chunk_length_13, b0_chunk_length_14, b0_chunk_length_15, b0_chunk_length_16, b0_chunk_length_17, b0_chunk_length_18]
  norm_num <;> ring
theorem b0_full_interpretation : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence5DenseCandidate.b0 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0 := by
  have parts : MazurTransfer.Order49Recurrence5DenseCandidate.b0Parts = List.replicate 1 0 ++ (b0_original_block_parts_0 ++ b0_original_block_parts_1) := by decide +kernel
  rw [b0_parts_match, parts]
  rw [toPolynomial_append, toPolynomial_append]
  simp only [toPolynomial_replicate_zero, List.length_replicate, b0_original_block_parts_0_length, zero_add]
  have combine (P Q : Polynomial ℚ) : (X : Polynomial ℚ) ^ 1 * (P + X ^ 57 * Q) = X ^ 1 * P + X ^ 58 * Q := by ring
  rw [combine, ← b0_original_block_parts_0_interpretation, ← b0_original_block_parts_1_interpretation]
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0
  exact add_comm _ _
private theorem b1_parts_match : MazurTransfer.Order49Recurrence5DenseCandidate.b1 = MazurTransfer.Order49Recurrence5DenseCandidate.b1Parts := by decide +kernel
private theorem b1_chunk_length_0 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk18).length = 5 := by rfl
private theorem b1_chunk_length_1 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk17).length = 8 := by rfl
private theorem b1_chunk_length_2 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk16).length = 8 := by rfl
private theorem b1_chunk_length_3 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk15).length = 8 := by rfl
private theorem b1_chunk_length_4 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk14).length = 8 := by rfl
private theorem b1_chunk_length_5 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk13).length = 8 := by rfl
private theorem b1_chunk_length_6 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk12).length = 8 := by rfl
private theorem b1_chunk_length_7 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk11).length = 8 := by rfl
private theorem b1_chunk_length_8 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk10).length = 8 := by rfl
private theorem b1_chunk_length_9 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk9).length = 8 := by rfl
private theorem b1_chunk_length_10 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk8).length = 8 := by rfl
private theorem b1_chunk_length_11 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk7).length = 8 := by rfl
private theorem b1_chunk_length_12 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk6).length = 8 := by rfl
private theorem b1_chunk_length_13 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk5).length = 8 := by rfl
private theorem b1_chunk_length_14 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk4).length = 8 := by rfl
private theorem b1_chunk_length_15 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk3).length = 8 := by rfl
private theorem b1_chunk_length_16 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk2).length = 8 := by rfl
private theorem b1_chunk_length_17 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk1).length = 8 := by rfl
private theorem b1_chunk_length_18 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk0).length = 8 := by rfl
private def b1_original_block_parts_0 : List ℤ := MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk18 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk17 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk16 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk15 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk14 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk13 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk12
private theorem b1_original_block_parts_0_length : b1_original_block_parts_0.length = 53 := by rfl
private theorem b1_original_block_parts_0_interpretation : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient1Block1 = (X : Polynomial ℚ) ^ 1 * MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial b1_original_block_parts_0 := by
  have h0 := MazurTransfer.order49_recurrence5_b1_original_chunk_interpretations.1.identity
  have h1 := MazurTransfer.order49_recurrence5_b1_original_chunk_interpretations.2.1.identity
  have h2 := MazurTransfer.order49_recurrence5_b1_original_chunk_interpretations.2.2.1.identity
  have h3 := MazurTransfer.order49_recurrence5_b1_original_chunk_interpretations.2.2.2.1.identity
  have h4 := MazurTransfer.order49_recurrence5_b1_original_chunk_interpretations.2.2.2.2.1.identity
  have h5 := MazurTransfer.order49_recurrence5_b1_original_chunk_interpretations.2.2.2.2.2.1.identity
  have h6 := MazurTransfer.order49_recurrence5_b1_original_chunk_interpretations.2.2.2.2.2.2.1.identity
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient1Block1
  rw [h0, h1, h2, h3, h4, h5, h6]
  simp only [b1_original_block_parts_0, toPolynomial_append, List.length_append, b1_chunk_length_0, b1_chunk_length_1, b1_chunk_length_2, b1_chunk_length_3, b1_chunk_length_4, b1_chunk_length_5]
  norm_num <;> ring
private def b1_original_block_parts_1 : List ℤ := MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk11 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk10 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk9 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk8 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk7 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk6 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk5 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk4 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk3 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk2 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk1 ++ MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient1Chunk0
private theorem b1_original_block_parts_1_length : b1_original_block_parts_1.length = 96 := by rfl
private theorem b1_original_block_parts_1_interpretation : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient1Block0 = (X : Polynomial ℚ) ^ 54 * MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial b1_original_block_parts_1 := by
  have h7 := MazurTransfer.order49_recurrence5_b1_original_chunk_interpretations.2.2.2.2.2.2.2.1.identity
  have h8 := MazurTransfer.order49_recurrence5_b1_original_chunk_interpretations.2.2.2.2.2.2.2.2.1.identity
  have h9 := MazurTransfer.order49_recurrence5_b1_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.1.identity
  have h10 := MazurTransfer.order49_recurrence5_b1_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.1.identity
  have h11 := MazurTransfer.order49_recurrence5_b1_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h12 := MazurTransfer.order49_recurrence5_b1_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h13 := MazurTransfer.order49_recurrence5_b1_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h14 := MazurTransfer.order49_recurrence5_b1_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h15 := MazurTransfer.order49_recurrence5_b1_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h16 := MazurTransfer.order49_recurrence5_b1_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h17 := MazurTransfer.order49_recurrence5_b1_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h18 := MazurTransfer.order49_recurrence5_b1_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.identity
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient1Block0
  rw [h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18]
  simp only [b1_original_block_parts_1, toPolynomial_append, List.length_append, b1_chunk_length_7, b1_chunk_length_8, b1_chunk_length_9, b1_chunk_length_10, b1_chunk_length_11, b1_chunk_length_12, b1_chunk_length_13, b1_chunk_length_14, b1_chunk_length_15, b1_chunk_length_16, b1_chunk_length_17]
  norm_num <;> ring
theorem b1_full_interpretation : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence5DenseCandidate.b1 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient1 := by
  have parts : MazurTransfer.Order49Recurrence5DenseCandidate.b1Parts = List.replicate 1 0 ++ (b1_original_block_parts_0 ++ b1_original_block_parts_1) := by decide +kernel
  rw [b1_parts_match, parts]
  rw [toPolynomial_append, toPolynomial_append]
  simp only [toPolynomial_replicate_zero, List.length_replicate, b1_original_block_parts_0_length, zero_add]
  have combine (P Q : Polynomial ℚ) : (X : Polynomial ℚ) ^ 1 * (P + X ^ 53 * Q) = X ^ 1 * P + X ^ 54 * Q := by ring
  rw [combine, ← b1_original_block_parts_0_interpretation, ← b1_original_block_parts_1_interpretation]
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient1
  exact add_comm _ _
private theorem b2_parts_match : MazurTransfer.Order49Recurrence5DenseCandidate.b2 = MazurTransfer.Order49Recurrence5DenseCandidate.b2Parts := by decide +kernel
private theorem b2_chunk_length_0 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient2Chunk18).length = 2 := by rfl
private theorem b2_chunk_length_1 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient2Chunk17).length = 8 := by rfl
private theorem b2_chunk_length_2 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient2Chunk16).length = 8 := by rfl
private theorem b2_chunk_length_3 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient2Chunk15).length = 8 := by rfl
private theorem b2_chunk_length_4 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient2Chunk14).length = 8 := by rfl
private theorem b2_chunk_length_5 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient2Chunk13).length = 8 := by rfl
private theorem b2_chunk_length_6 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient2Chunk12).length = 8 := by rfl
private theorem b2_chunk_length_7 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient2Chunk11).length = 8 := by rfl
private theorem b2_chunk_length_8 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient2Chunk10).length = 8 := by rfl
private theorem b2_chunk_length_9 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient2Chunk9).length = 8 := by rfl
private theorem b2_chunk_length_10 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient2Chunk8).length = 8 := by rfl
private theorem b2_chunk_length_11 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient2Chunk7).length = 8 := by rfl
private theorem b2_chunk_length_12 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient2Chunk6).length = 8 := by rfl
private theorem b2_chunk_length_13 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient2Chunk5).length = 8 := by rfl
private theorem b2_chunk_length_14 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient2Chunk4).length = 8 := by rfl
private theorem b2_chunk_length_15 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient2Chunk3).length = 8 := by rfl
private theorem b2_chunk_length_16 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient2Chunk2).length = 8 := by rfl
private theorem b2_chunk_length_17 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient2Chunk1).length = 8 := by rfl
private theorem b2_chunk_length_18 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder6Coefficient2Chunk0).length = 8 := by rfl
theorem b2_full_interpretation : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence5DenseCandidate.b2 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2 := by
  rw [b2_parts_match]
  simp only [MazurTransfer.Order49Recurrence5DenseCandidate.b2Parts, toPolynomial_append, toPolynomial_replicate_zero, List.length_append, List.length_replicate, b2_chunk_length_0, b2_chunk_length_1, b2_chunk_length_2, b2_chunk_length_3, b2_chunk_length_4, b2_chunk_length_5, b2_chunk_length_6, b2_chunk_length_7, b2_chunk_length_8, b2_chunk_length_9, b2_chunk_length_10, b2_chunk_length_11, b2_chunk_length_12, b2_chunk_length_13, b2_chunk_length_14, b2_chunk_length_15, b2_chunk_length_16, b2_chunk_length_17, b2_chunk_length_18]
  have h0 := MazurTransfer.order49_recurrence5_b2_original_chunk_interpretations.1.identity
  have h1 := MazurTransfer.order49_recurrence5_b2_original_chunk_interpretations.2.1.identity
  have h2 := MazurTransfer.order49_recurrence5_b2_original_chunk_interpretations.2.2.1.identity
  have h3 := MazurTransfer.order49_recurrence5_b2_original_chunk_interpretations.2.2.2.1.identity
  have h4 := MazurTransfer.order49_recurrence5_b2_original_chunk_interpretations.2.2.2.2.1.identity
  have h5 := MazurTransfer.order49_recurrence5_b2_original_chunk_interpretations.2.2.2.2.2.1.identity
  have h6 := MazurTransfer.order49_recurrence5_b2_original_chunk_interpretations.2.2.2.2.2.2.1.identity
  have h7 := MazurTransfer.order49_recurrence5_b2_original_chunk_interpretations.2.2.2.2.2.2.2.1.identity
  have h8 := MazurTransfer.order49_recurrence5_b2_original_chunk_interpretations.2.2.2.2.2.2.2.2.1.identity
  have h9 := MazurTransfer.order49_recurrence5_b2_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.1.identity
  have h10 := MazurTransfer.order49_recurrence5_b2_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.1.identity
  have h11 := MazurTransfer.order49_recurrence5_b2_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h12 := MazurTransfer.order49_recurrence5_b2_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h13 := MazurTransfer.order49_recurrence5_b2_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h14 := MazurTransfer.order49_recurrence5_b2_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h15 := MazurTransfer.order49_recurrence5_b2_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h16 := MazurTransfer.order49_recurrence5_b2_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h17 := MazurTransfer.order49_recurrence5_b2_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.identity
  have h18 := MazurTransfer.order49_recurrence5_b2_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.identity
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2Block1 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2Block0
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18]
  norm_num <;> ring
private theorem c0_parts_match : MazurTransfer.Order49Recurrence5DenseCandidate.c0 = MazurTransfer.Order49Recurrence5DenseCandidate.c0Parts := by decide +kernel
private theorem c0_chunk_length_0 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder7Coefficient0Chunk11).length = 1 := by rfl
private theorem c0_chunk_length_1 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder7Coefficient0Chunk10).length = 8 := by rfl
private theorem c0_chunk_length_2 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder7Coefficient0Chunk9).length = 8 := by rfl
private theorem c0_chunk_length_3 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder7Coefficient0Chunk8).length = 8 := by rfl
private theorem c0_chunk_length_4 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder7Coefficient0Chunk7).length = 8 := by rfl
private theorem c0_chunk_length_5 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder7Coefficient0Chunk6).length = 8 := by rfl
private theorem c0_chunk_length_6 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder7Coefficient0Chunk5).length = 8 := by rfl
private theorem c0_chunk_length_7 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder7Coefficient0Chunk4).length = 8 := by rfl
private theorem c0_chunk_length_8 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder7Coefficient0Chunk3).length = 8 := by rfl
private theorem c0_chunk_length_9 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder7Coefficient0Chunk2).length = 8 := by rfl
private theorem c0_chunk_length_10 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder7Coefficient0Chunk1).length = 8 := by rfl
private theorem c0_chunk_length_11 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder7Coefficient0Chunk0).length = 8 := by rfl
theorem c0_full_interpretation : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence5DenseCandidate.c0 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0 := by
  rw [c0_parts_match]
  simp only [MazurTransfer.Order49Recurrence5DenseCandidate.c0Parts, toPolynomial_append, toPolynomial_replicate_zero, List.length_append, List.length_replicate, c0_chunk_length_0, c0_chunk_length_1, c0_chunk_length_2, c0_chunk_length_3, c0_chunk_length_4, c0_chunk_length_5, c0_chunk_length_6, c0_chunk_length_7, c0_chunk_length_8, c0_chunk_length_9, c0_chunk_length_10, c0_chunk_length_11]
  have h0 := MazurTransfer.order49_recurrence5_c0_original_chunk_interpretations.1.identity
  have h1 := MazurTransfer.order49_recurrence5_c0_original_chunk_interpretations.2.1.identity
  have h2 := MazurTransfer.order49_recurrence5_c0_original_chunk_interpretations.2.2.1.identity
  have h3 := MazurTransfer.order49_recurrence5_c0_original_chunk_interpretations.2.2.2.1.identity
  have h4 := MazurTransfer.order49_recurrence5_c0_original_chunk_interpretations.2.2.2.2.1.identity
  have h5 := MazurTransfer.order49_recurrence5_c0_original_chunk_interpretations.2.2.2.2.2.1.identity
  have h6 := MazurTransfer.order49_recurrence5_c0_original_chunk_interpretations.2.2.2.2.2.2.1.identity
  have h7 := MazurTransfer.order49_recurrence5_c0_original_chunk_interpretations.2.2.2.2.2.2.2.1.identity
  have h8 := MazurTransfer.order49_recurrence5_c0_original_chunk_interpretations.2.2.2.2.2.2.2.2.1.identity
  have h9 := MazurTransfer.order49_recurrence5_c0_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.1.identity
  have h10 := MazurTransfer.order49_recurrence5_c0_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.1.identity
  have h11 := MazurTransfer.order49_recurrence5_c0_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.2.identity
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0Block0
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  norm_num <;> ring
private theorem c1_parts_match : MazurTransfer.Order49Recurrence5DenseCandidate.c1 = MazurTransfer.Order49Recurrence5DenseCandidate.c1Parts := by decide +kernel
private theorem c1_chunk_length_0 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder7Coefficient1Chunk10).length = 5 := by rfl
private theorem c1_chunk_length_1 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder7Coefficient1Chunk9).length = 8 := by rfl
private theorem c1_chunk_length_2 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder7Coefficient1Chunk8).length = 8 := by rfl
private theorem c1_chunk_length_3 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder7Coefficient1Chunk7).length = 8 := by rfl
private theorem c1_chunk_length_4 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder7Coefficient1Chunk6).length = 8 := by rfl
private theorem c1_chunk_length_5 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder7Coefficient1Chunk5).length = 8 := by rfl
private theorem c1_chunk_length_6 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder7Coefficient1Chunk4).length = 8 := by rfl
private theorem c1_chunk_length_7 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder7Coefficient1Chunk3).length = 8 := by rfl
private theorem c1_chunk_length_8 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder7Coefficient1Chunk2).length = 8 := by rfl
private theorem c1_chunk_length_9 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder7Coefficient1Chunk1).length = 8 := by rfl
private theorem c1_chunk_length_10 : (MazurTransfer.Order49Recurrence5DenseCandidate.chunk_remainder7Coefficient1Chunk0).length = 8 := by rfl
theorem c1_full_interpretation : MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence5DenseCandidate.c1 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1 := by
  rw [c1_parts_match]
  simp only [MazurTransfer.Order49Recurrence5DenseCandidate.c1Parts, toPolynomial_append, toPolynomial_replicate_zero, List.length_append, List.length_replicate, c1_chunk_length_0, c1_chunk_length_1, c1_chunk_length_2, c1_chunk_length_3, c1_chunk_length_4, c1_chunk_length_5, c1_chunk_length_6, c1_chunk_length_7, c1_chunk_length_8, c1_chunk_length_9, c1_chunk_length_10]
  have h0 := MazurTransfer.order49_recurrence5_c1_original_chunk_interpretations.1.identity
  have h1 := MazurTransfer.order49_recurrence5_c1_original_chunk_interpretations.2.1.identity
  have h2 := MazurTransfer.order49_recurrence5_c1_original_chunk_interpretations.2.2.1.identity
  have h3 := MazurTransfer.order49_recurrence5_c1_original_chunk_interpretations.2.2.2.1.identity
  have h4 := MazurTransfer.order49_recurrence5_c1_original_chunk_interpretations.2.2.2.2.1.identity
  have h5 := MazurTransfer.order49_recurrence5_c1_original_chunk_interpretations.2.2.2.2.2.1.identity
  have h6 := MazurTransfer.order49_recurrence5_c1_original_chunk_interpretations.2.2.2.2.2.2.1.identity
  have h7 := MazurTransfer.order49_recurrence5_c1_original_chunk_interpretations.2.2.2.2.2.2.2.1.identity
  have h8 := MazurTransfer.order49_recurrence5_c1_original_chunk_interpretations.2.2.2.2.2.2.2.2.1.identity
  have h9 := MazurTransfer.order49_recurrence5_c1_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.1.identity
  have h10 := MazurTransfer.order49_recurrence5_c1_original_chunk_interpretations.2.2.2.2.2.2.2.2.2.2.identity
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1Block0
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  norm_num <;> ring
end MazurTransfer.Order49Recurrence5DenseCandidate.FullTableProof

theorem solution : MazurTransfer.ExactEqualityCertificate (α := Polynomial ℚ) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence5DenseCandidate.b0) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0) ∧
    MazurTransfer.ExactEqualityCertificate (α := Polynomial ℚ) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence5DenseCandidate.b1) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient1) ∧
    MazurTransfer.ExactEqualityCertificate (α := Polynomial ℚ) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence5DenseCandidate.b2) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2) ∧
    MazurTransfer.ExactEqualityCertificate (α := Polynomial ℚ) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence5DenseCandidate.c0) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0) ∧
    MazurTransfer.ExactEqualityCertificate (α := Polynomial ℚ) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence5DenseCandidate.c1) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1) := by
  exact ⟨⟨MazurTransfer.Order49Recurrence5DenseCandidate.FullTableProof.b0_full_interpretation⟩, ⟨⟨MazurTransfer.Order49Recurrence5DenseCandidate.FullTableProof.b1_full_interpretation⟩, ⟨⟨MazurTransfer.Order49Recurrence5DenseCandidate.FullTableProof.b2_full_interpretation⟩, ⟨⟨MazurTransfer.Order49Recurrence5DenseCandidate.FullTableProof.c0_full_interpretation⟩, ⟨MazurTransfer.Order49Recurrence5DenseCandidate.FullTableProof.c1_full_interpretation⟩⟩⟩⟩⟩
#print axioms solution
