-- Prove2me | solution 1 for KLZ97.levelError_eq_threshold_pow
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T07:45:43.899209+00:00
-- url     : https://prove2.me/submissions/dfdb1069-ccea-40e4-a408-c8ea4476d305

import Mathlib
import Definitions.Def_KLZ97_model

open KLZ97

namespace Ag2Aux_KLZThrPow

theorem closed (f p : ℝ) (h : ℕ) :
    levelError f p h = f ^ (2 ^ h - 1) * p ^ (2 ^ h) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [levelError_succ, ih]
    have h1 : 1 ≤ 2 ^ h := Nat.one_le_two_pow
    have h2 : 2 ^ (h + 1) - 1 = 2 * (2 ^ h - 1) + 1 := by rw [pow_succ]; omega
    rw [h2, show 2 ^ (h + 1) = 2 ^ h * 2 by ring, pow_add, pow_mul, pow_mul]
    ring

end Ag2Aux_KLZThrPow

open Ag2Aux_KLZThrPow

theorem solution (f p : ℝ) (hf : f ≠ 0) (h : ℕ) :
    levelError f p h = (f * p) ^ (2 ^ h) / f := by
  rw [closed, mul_pow]
  have h1 : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  have : f ^ (2 ^ h) = f ^ (2 ^ h - 1) * f := by
    rw [← pow_succ]; congr 1; omega
  rw [this]; field_simp
