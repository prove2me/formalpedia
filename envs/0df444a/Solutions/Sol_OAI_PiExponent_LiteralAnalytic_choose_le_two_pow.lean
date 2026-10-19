-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.choose_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T16:32:50.144974+00:00
-- url     : https://prove2.me/submissions/03c44c7b-bd94-4713-8bff-b610fc3fd6b1

import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Bounds

theorem solution (k n : ℕ) :
    (Nat.choose (k + n) k : ℝ) ≤ (2 : ℝ) ^ (k + n) := by
  exact_mod_cast (Nat.choose_le_two_pow (k + n) k)