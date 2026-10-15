-- Prove2me | solution 1 for OAI.PiExponent.eventually_integer_geometric_window
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T09:37:17.339245+00:00
-- url     : https://prove2.me/submissions/950a3538-65bf-4a6e-84f2-607df5d06a2c

import Mathlib.Data.Real.Basic
import Theorems.Thm_OAI_PiExponent_real_geometric_window_eventually
import Theorems.Thm_OAI_PiExponent_round_nat_in_strict_window

theorem solution
    (theta b : ℝ) (htheta : 0 < theta) (htheta_one : theta < 1)
    (hb : 0 < b) (hgap : b ^ 2 * theta < 1) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      ∃ K : ℕ, 0 < K ∧
        (K : ℝ) ^ 2 * theta ^ m < 1 ∧ b ^ m / 8 < (K : ℝ) := by
  obtain ⟨M, hM⟩ := OAI.PiExponent.real_geometric_window_eventually
    theta b htheta htheta_one hb hgap
  refine ⟨M, ?_⟩
  intro m hm
  have hx : 0 < b ^ m / 8 := div_pos (pow_pos hb m) (by norm_num)
  have hq : 0 < theta ^ m := pow_pos htheta m
  exact OAI.PiExponent.round_nat_in_strict_window
    (b ^ m / 8) (theta ^ m) hx hq (hM m hm)