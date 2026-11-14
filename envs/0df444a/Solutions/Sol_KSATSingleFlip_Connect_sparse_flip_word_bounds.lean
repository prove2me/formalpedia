-- Prove2me | solution 1 for KSATSingleFlip.Connect.sparse_flip_word_bounds
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:27:53.131199+00:00
-- url     : https://prove2.me/submissions/4f3a8a81-c6e6-41e9-8638-6c7ef5b5afdf

import Definitions.Def_KSATSingleFlip_Connect_SparseFlip

open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- Sparse inputs with m=O(n) and compact logarithmic flip lists have linear
abstract word size, without asserting any algorithmic running time. -/
theorem audit_sparse_flip_word_bounds (n k m c : ℕ) (hn : 0 < n) (hm : m ≤ c * n) :
    sparseFlipInputWords n k m ≤ 4 + (2 * k * c + 1) * n ∧
    ∀ (p : FlipListPath n) (A : ℝ), 0 ≤ A →
      (p.flips.length : ℝ) ≤ A * Real.log n →
      (p.wordCount : ℝ) ≤ (1 + A) * n + 1 := by
  constructor
  · unfold sparseFlipInputWords
    nlinarith
  · intro p A hA hp
    have hlog : Real.log (n : ℝ) ≤ n := Real.log_le_self (Nat.cast_nonneg _)
    have hmul := mul_le_mul_of_nonneg_left hlog hA
    simp only [FlipListPath.wordCount, Nat.cast_add, Nat.cast_one]
    nlinarith

end KSATSingleFlip.Connect

open KSATSingleFlip.Connect

theorem solution (n k m c : ℕ) (hn : 0 < n) (hm : m ≤ c * n) :
    sparseFlipInputWords n k m ≤ 4 + (2 * k * c + 1) * n ∧
    ∀ (p : FlipListPath n) (A : ℝ), 0 ≤ A →
      (p.flips.length : ℝ) ≤ A * Real.log n →
      (p.wordCount : ℝ) ≤ (1 + A) * n + 1 := by
  exact audit_sparse_flip_word_bounds n k m c hn hm

#print axioms solution
