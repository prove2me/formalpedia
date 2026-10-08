-- Prove2me | solution 1 for HlawkaSchatten.LpThreshold.hlawka_fails_above
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T02:30:58.146217+00:00
-- url     : https://prove2.me/submissions/eeaeeecb-5ce0-4a82-9148-e00241479d03

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

/-- `lpNorm` of a vector whose three entries all have absolute value `c`. -/
lemma hlawkaThreshold_lpNorm_const {p c : ℝ} (hp : 0 < p) (hc : 0 ≤ c)
    (v : Fin 3 → ℝ) (hv : ∀ i, |v i| = c) :
    lpNorm p v = (3 : ℝ) ^ (1 / p) * c := by
  unfold lpNorm
  simp only [Real.norm_eq_abs, hv, Fin.sum_univ_three]
  rw [show c ^ p + c ^ p + c ^ p = 3 * c ^ p by ring,
    Real.mul_rpow (by norm_num) (Real.rpow_nonneg hc p), ← Real.rpow_mul hc,
    mul_one_div_cancel hp.ne', Real.rpow_one]

/-- `lpNorm` of a vector with a single nonzero entry `2` (up to sign). -/
lemma hlawkaThreshold_lpNorm_single {p : ℝ} (hp : 0 < p) (v : Fin 3 → ℝ) (k : Fin 3)
    (hk : |v k| = 2) (hz : ∀ i, i ≠ k → v i = 0) :
    lpNorm p v = 2 := by
  unfold lpNorm
  have hsum : ∑ i, ‖v i‖ ^ p = (2 : ℝ) ^ p := by
    rw [Finset.sum_eq_single k]
    · rw [Real.norm_eq_abs, hk]
    · intro i _ hik
      rw [hz i hik, norm_zero, Real.zero_rpow hp.ne']
    · simp
  rw [hsum, ← Real.rpow_mul (by norm_num), mul_one_div_cancel hp.ne', Real.rpow_one]

theorem solution :
    ∀ p : ℝ, Real.log 3 / Real.log (3 / 2) < p →
      ¬ HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) 1 := by
  intro p hp h
  have hlog32 : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hp0 : 0 < p := lt_trans (div_pos hlog3 hlog32) hp
  -- the root `r = 3^(1/p)` is below `3/2`
  have hr : (3 : ℝ) ^ (1 / p) < 3 / 2 := by
    rw [div_lt_iff₀ hlog32] at hp
    rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)]
    apply Real.exp_lt_exp.mpr
    rw [one_div, ← div_eq_mul_inv, div_lt_iff₀ hp0]
    linarith
  set x : Fin 3 → ℝ := ![-1, 1, 1]
  set y : Fin 3 → ℝ := ![1, -1, 1]
  set z : Fin 3 → ℝ := ![1, 1, -1]
  have hx := hlawkaThreshold_lpNorm_const hp0 zero_le_one x (by intro i; fin_cases i <;> simp [x])
  have hy := hlawkaThreshold_lpNorm_const hp0 zero_le_one y (by intro i; fin_cases i <;> simp [y])
  have hz := hlawkaThreshold_lpNorm_const hp0 zero_le_one z (by intro i; fin_cases i <;> simp [z])
  have hxyz := hlawkaThreshold_lpNorm_const hp0 zero_le_one (x + y + z)
    (by intro i; fin_cases i <;> simp [x, y, z])
  have hxy := hlawkaThreshold_lpNorm_single hp0 (x + y) 2
    (by simp [x, y]; norm_num) (by intro i hi; fin_cases i <;> simp_all [x, y])
  have hxz := hlawkaThreshold_lpNorm_single hp0 (x + z) 1
    (by simp [x, z]; norm_num) (by intro i hi; fin_cases i <;> simp_all [x, z])
  have hyz := hlawkaThreshold_lpNorm_single hp0 (y + z) 0
    (by simp [y, z]; norm_num) (by intro i hi; fin_cases i <;> simp_all [y, z])
  have hh := h x y z
  simp only [tripleGap, pairGapSum, pairGap, hx, hy, hz, hxyz, hxy, hxz, hyz] at hh
  linarith
