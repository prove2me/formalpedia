-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.sum_choose_weighted_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:44:05.020705+00:00
-- url     : https://prove2.me/submissions/3585964d-0a66-4869-844e-c39f7b1b56ea

import Mathlib
import Mathlib.Data.Nat.Choose.Sum

open scoped BigOperators
theorem solution
    (k n : ℕ) (hk : 1 ≤ k) :
    ∑ r ∈ Finset.range (n + 1), Nat.choose (r + k - 1) r =
      Nat.choose (n + k) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, show n + 1 + k - 1 = n + k by omega,
      show n + 1 + k = (n + k) + 1 by omega, Nat.choose_succ_succ']
