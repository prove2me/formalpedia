-- Prove2me | solution 1 for KempeCloning.binomial_normalization
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T14:09:35.191269+00:00
-- url     : https://prove2.me/submissions/2340b6d6-44e7-4ee3-8043-b5e7d7c0ce3b

import Mathlib

theorem solution (m l : ℕ) :
    ∑ i ∈ Finset.range (l + 1), (m + i).choose m = (m + l + 1).choose l := by
  have hsymm : (m + l + 1).choose l = (m + l + 1).choose (m + 1) := by
    apply Nat.choose_symm_of_eq_add
    omega
  rw [hsymm]
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (Nat.sum_range_add_choose l m)
