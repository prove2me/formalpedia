-- Prove2me | solution 1 for LL_Decomp1528c.theta_two_mul_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:05.714399+00:00
-- url     : https://prove2.me/submissions/1074f4a6-258f-4231-b337-d21da71b83cc

import Mathlib

open Real Finset Chebyshev

theorem ChMeAux.theta_two_mul_sub_le (n : ℕ) : θ (2 * n) - θ n ≤ n * log 4 := by
  have h2 : (2 * (n : ℝ)) = ((n + n : ℕ) : ℝ) := by push_cast; ring
  rw [h2, theta_eq_log_primorial, theta_eq_log_primorial, Nat.floor_natCast, Nat.floor_natCast]
  have h1 : primorial (n + n) ≤ primorial n * 4 ^ n :=
    (primorial_add_le le_rfl).trans (Nat.mul_le_mul_left _
      (by simpa [two_mul] using Nat.choose_le_centralBinom n n |>.trans (Nat.centralBinom_le_four_pow n)))
  have hp := primorial_pos n
  have h3 : log (primorial (n + n)) ≤ log (primorial n) + n * log 4 := by
    rw [← Real.log_pow, ← Real.log_mul (by exact_mod_cast hp.ne') (by positivity)]
    exact Real.log_le_log (by exact_mod_cast primorial_pos _) (by exact_mod_cast h1)
  linarith

theorem solution (n : ℕ) : θ (2 * n) - θ n ≤ n * log 4 := ChMeAux.theta_two_mul_sub_le n
