-- Prove2me | solution 1 for InnovContest.Rewards.rank_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:50:25.17953+00:00
-- url     : https://prove2.me/submissions/b2cbae6a-48f3-47bb-afa0-795b098b4a32

import Mathlib
import Definitions.Def_InnovContest_Rewards_OrderStats

set_option autoImplicit false
open InnovContest.Rewards

theorem solution (n j : ℕ) (hn : 2 ≤ n) (hj1 : 1 ≤ j) (hjn : j ≤ n)
    (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    ordCDF (n - 1) (n - j) q - ordCDF (n - 1) (n - j + 1) q =
      ((n - 1).choose (j - 1) : ℝ) * q ^ (n - j) * (1 - q) ^ (j - 1) := by
  have hk : n - j ≤ n - 1 := by omega
  have hsplit : ordCDF (n - 1) (n - j) q = ((n - 1).choose (n - j) : ℝ) * q ^ (n - j) * (1 - q) ^ ((n - 1) - (n - j)) + ordCDF (n - 1) (n - j + 1) q := by
    unfold ordCDF
    have : Finset.Icc (n - j) (n - 1) = insert (n - j) (Finset.Icc (n - j + 1) (n - 1)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [this, Finset.sum_insert (by simp)]
  have hc : (n - 1).choose (n - j) = (n - 1).choose (j - 1) := by
    have := Nat.choose_symm (n := n - 1) (k := j - 1) (by omega)
    rw [← this]; congr 1; omega
  have he : (n - 1) - (n - j) = j - 1 := by omega
  rw [hsplit, hc, he]; ring
