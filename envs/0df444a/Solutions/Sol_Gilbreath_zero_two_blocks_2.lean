-- Prove2me | solution 2 for Gilbreath.zero_two_blocks
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @EvanLLL
-- created : 2026-09-25T14:11:13.641388+00:00
-- url     : https://prove2.me/submissions/a24afd1d-3db6-44b6-a12d-6a620d1ae868
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Gilbreath_prime_gap_positive_normalization
import Theorems.Thm_Gilbreath_iterAbsDiff_shift_mul
import Theorems.Thm_Gilbreath_normalized_prime_gap_binary_head

set_option autoImplicit false
open Gilbreath

theorem solution (K : ℕ) : ∃ k m : ℕ, 1 ≤ k ∧ k + m = K + 1 ∧
    ∀ n, 1 ≤ n → n ≤ m + 1 → d k n = 0 ∨ d k n = 2 := by
  obtain ⟨b, hb, _⟩ := prime_gap_positive_normalization
  have hd : d (K + 1) = iterAbsDiff (d 1) K := by
    simpa [Nat.add_comm] using (iterAbsDiff_d 1 K).symm
  have hs := iterAbsDiff_shift_mul (d 1) 1 1 K 0
  simp only [Nat.one_mul, Nat.zero_add] at hs
  have hg := iterAbsDiff_shift_mul b 2 0 K 0
  simp only [Nat.add_zero] at hg
  have heq : (fun j => d 1 (j + 1)) = (fun j => 2 * b j) := by
    funext j
    exact hb.1 j
  have key : d (K + 1) 1 = 2 * iterAbsDiff b K 0 := by
    rw [hd, ← hs, heq, hg]
  refine ⟨K + 1, 0, by omega, by omega, ?_⟩
  intro n hn hn'
  have hn1 : n = 1 := by omega
  subst n
  rcases normalized_prime_gap_binary_head b hb.1 K with hz | ho
  · left
    simpa [hz] using key
  · right
    simpa [ho] using key

#print axioms solution
