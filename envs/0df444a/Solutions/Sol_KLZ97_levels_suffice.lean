-- Prove2me | solution 1 for KLZ97.levels_suffice
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T07:47:23.02793+00:00
-- url     : https://prove2.me/submissions/d4068965-fe58-447d-82ff-ea88afc779a3

import Mathlib
import Definitions.Def_KLZ97_model

open KLZ97

theorem solution (f p q : ℝ) (n : ℕ) (h : ℕ) (hp : 0 < f * p) (hfp : f * p < 1)
    (hq : 0 < q) (hqn : q < n)
    (hlevels : Real.log ((n : ℝ) / q) / Real.log (1 / (f * p)) < (2 : ℝ) ^ h) :
    (n : ℝ) * (f * p) ^ (2 ^ h) < q := by
  have hn : (0 : ℝ) < n := lt_trans hq hqn
  have hL : 0 < Real.log (1 / (f * p)) := Real.log_pos (by rw [lt_div_iff₀ hp]; linarith)
  rw [div_lt_iff₀ hL] at hlevels
  rw [one_div, Real.log_inv] at hlevels
  have hx : 0 < (n : ℝ) / q * (f * p) ^ (2 ^ h) := by positivity
  have hlog : Real.log ((n : ℝ) / q * (f * p) ^ (2 ^ h)) < 0 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    linarith
  have := (Real.log_neg_iff hx).1 hlog
  rw [div_mul_eq_mul_div, div_lt_one hq] at this
  exact this
