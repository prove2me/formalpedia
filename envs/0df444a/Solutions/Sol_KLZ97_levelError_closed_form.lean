-- Prove2me | solution 1 for KLZ97.levelError_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T07:45:43.999447+00:00
-- url     : https://prove2.me/submissions/8d0a843f-f8d3-4037-a813-84fa38bba50d

import Mathlib
import Definitions.Def_KLZ97_model

open KLZ97

theorem solution (f p : ℝ) (h : ℕ) :
    levelError f p h = f ^ (2 ^ h - 1) * p ^ (2 ^ h) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [levelError_succ, ih]
    have h1 : 1 ≤ 2 ^ h := Nat.one_le_two_pow
    have h2 : 2 ^ (h + 1) - 1 = 2 * (2 ^ h - 1) + 1 := by rw [pow_succ]; omega
    rw [h2, show 2 ^ (h + 1) = 2 ^ h * 2 by ring, pow_add, pow_mul, pow_mul]
    ring
