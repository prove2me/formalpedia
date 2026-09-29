-- Prove2me | solution 1 for Gilbreath.normalized_prime_gap_binary_head
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @EvanLLL
-- created : 2026-09-26T00:15:09.67601+00:00
-- url     : https://prove2.me/submissions/3e9edb8d-6f2d-4f19-a7ab-3c5b14fbdd9f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Gilbreath_extension_bottom_identity
import Theorems.Thm_Gilbreath_extension_interval_criterion
import Theorems.Thm_Gilbreath_prime_gap_ordered_extension_condition
import Theorems.Thm_Gilbreath_prime_gap_next_extension_bound

set_option autoImplicit false
open Gilbreath

theorem solution (b : ℕ → ℕ)
    (hb : ∀ n, d 1 (n + 1) = 2 * b n) (k : ℕ) :
    iterAbsDiff b k 0 = 0 ∨ iterAbsDiff b k 0 = 1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      have hp : ∀ j, j < k → iterAbsDiff b j 0 ≤ 1 := by
        intro j hj
        rcases ih j hj with hz | ho <;> omega
      have hiff := (extension_interval_criterion (extensionBoundary b k)).mpr (prime_gap_ordered_extension_condition b hb k hp)
      have hf := (hiff (b k)).mpr (prime_gap_next_extension_bound b hb k hp)
      rw [extension_bottom_identity b k] at hf
      omega

#print axioms solution
