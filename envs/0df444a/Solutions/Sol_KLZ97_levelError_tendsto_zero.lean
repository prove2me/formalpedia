-- Prove2me | solution 1 for KLZ97.levelError_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T07:45:44.006477+00:00
-- url     : https://prove2.me/submissions/3d43c4a1-46d2-4e43-9c17-1caeab70321c

import Mathlib
import Definitions.Def_KLZ97_model

open KLZ97

namespace Ag2Aux_KLZTends

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

theorem thr (f p : ℝ) (hf : f ≠ 0) (h : ℕ) :
    levelError f p h = (f * p) ^ (2 ^ h) / f := by
  rw [closed, mul_pow]
  have h1 : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  have : f ^ (2 ^ h) = f ^ (2 ^ h - 1) * f := by
    rw [← pow_succ]; congr 1; omega
  rw [this]; field_simp

end Ag2Aux_KLZTends

open Ag2Aux_KLZTends

theorem solution (f p : ℝ) (hf : 0 < f) (hp : 0 ≤ p) (hfp : f * p < 1) :
    Filter.Tendsto (levelError f p) Filter.atTop (nhds 0) := by
  have e : levelError f p = fun h => (f * p) ^ (2 ^ h) / f := by
    funext h; exact thr f p hf.ne' h
  rw [e]
  have h1 : Filter.Tendsto (fun n : ℕ => (f * p) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hfp
  have h2 : Filter.Tendsto (fun h : ℕ => 2 ^ h) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have := (h1.comp h2).div_const f
  simpa using this
