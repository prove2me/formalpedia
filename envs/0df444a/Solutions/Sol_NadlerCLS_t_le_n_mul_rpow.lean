-- Prove2me | solution 1 for NadlerCLS.t_le_n_mul_rpow
-- status  : ACCEPTED   (prove)
-- author  : @utkuokur
-- created : 2026-11-10T10:57:21.799645+00:00
-- url     : https://prove2.me/submissions/e8c91436-40f0-4537-996e-d4a5ab721d6f

import Mathlib

set_option autoImplicit false

theorem solution (n : ℕ) (hn : 1 ≤ n) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (t : ℝ)
    (ht0 : 0 < t) (htn : t ≤ n) : t ≤ (n : ℝ) * t ^ β := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 ≤ t ^ β := by positivity
  rcases le_total t 1 with h | h
  · have h1 : t ≤ t ^ β := by
      calc t = t ^ (1 : ℝ) := (Real.rpow_one t).symm
        _ ≤ t ^ β := Real.rpow_le_rpow_of_exponent_ge ht0 h hβ1
    nlinarith
  · have h1 : 1 ≤ t ^ β := Real.one_le_rpow h hβ0.le
    nlinarith
