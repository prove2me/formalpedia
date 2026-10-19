-- Prove2me | solution 1 for OAI.PiExponent.rational_scale_error_control_nat_n
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:45:30.029994+00:00
-- url     : https://prove2.me/submissions/459ccdce-e45c-45a4-8fbe-5483d1358f0d

import Mathlib
import Mathlib.Data.Real.Basic

theorem solution
    (d g : ℝ) (hd : 0 ≤ d) (hg : 0 < g) :
    ∃ n : ℕ, 0 < n ∧ d / (n : ℝ) < g / 4 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (4 * d / g)
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  have hn1 : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  rw [div_lt_iff₀ hn1]
  have h4 : 4 * d < g * n := by rw [div_lt_iff₀ hg] at hn; linarith
  push_cast
  nlinarith
