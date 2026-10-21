-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.analyticColumn_exponential_factor_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T13:40:44.124099+00:00
-- url     : https://prove2.me/submissions/af39c9cc-7327-4eb1-8191-8925edafbfc2

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic

open OAI.PiExponent.FinitePeriodCollision

theorem solution
    (h : ℕ) {R : ℝ} (z : ℂ) (hR : 1 ≤ R) (hz : ‖z‖ ≤ R) :
    ‖Complex.exp ((h : ℂ) * z)‖ ≤ Real.exp ((h : ℝ) * R) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    ((h : ℂ) * z).re = (h : ℝ) * z.re := by simp
    _ ≤ (h : ℝ) * R :=
      mul_le_mul_of_nonneg_left (Complex.re_le_norm z |>.trans hz)
        (Nat.cast_nonneg h)