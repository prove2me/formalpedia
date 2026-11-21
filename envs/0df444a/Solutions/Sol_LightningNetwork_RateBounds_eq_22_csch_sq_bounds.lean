-- Prove2me | solution 1 for LightningNetwork.RateBounds.eq_22_csch_sq_bounds
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T03:26:32.683287+00:00
-- url     : https://prove2.me/submissions/15367491-54a0-4861-a9e2-d0f35041ab99

import Mathlib

open Real MeasureTheory

set_option maxHeartbeats 2000000

private lemma six_pow_le_factorial (n : ℕ) : 6 ^ n ≤ (2 * n + 1).factorial := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have h2 : (2 * (k + 1) + 1).factorial = (2 * k + 3).factorial := by ring_nf
    rw [h2]
    have h3 : (2 * k + 3).factorial = (2 * k + 3) * (2 * k + 2) * (2 * k + 1).factorial := by
      rw [show 2 * k + 3 = (2 * k + 2) + 1 by ring, Nat.factorial_succ]
      rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, Nat.factorial_succ]
      ring
    rw [h3]
    have h4 : 6 ≤ (2 * k + 3) * (2 * k + 2) := by nlinarith
    have h5 : 0 < (2 * k + 1).factorial := Nat.factorial_pos _
    nlinarith

/-- `sinh x ≤ x / (1 - x²/6)` for `x² < 6`, from the Taylor series of `sinh`. -/
private lemma sinh_le_div (x : ℝ) (hx : 0 < x) (h6 : x ^ 2 < 6) :
    Real.sinh x ≤ x / (1 - x ^ 2 / 6) := by
  have hx2 : 0 < x ^ 2 := by positivity
  have hr0 : 0 ≤ x ^ 2 / 6 := by positivity
  have hr1 : x ^ 2 / 6 < 1 := by nlinarith
  have hgeom : Summable (fun n : ℕ => (x ^ 2 / 6) ^ n) :=
    summable_geometric_of_lt_one hr0 hr1
  have hterm : ∀ n : ℕ, x ^ (2 * n) / ((2 * n + 1).factorial : ℝ) ≤ (x ^ 2 / 6) ^ n := by
    intro n
    have hfac : (6 : ℝ) ^ n ≤ ((2 * n + 1).factorial : ℝ) := by
      exact_mod_cast six_pow_le_factorial n
    have h6n : (0 : ℝ) < (6 : ℝ) ^ n := by positivity
    rw [div_pow, ← pow_mul]
    exact div_le_div_of_nonneg_left (by positivity) h6n hfac
  have hsumm2 : Summable (fun n : ℕ => x ^ (2 * n) / ((2 * n + 1).factorial : ℝ)) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hterm hgeom
  calc Real.sinh x = ∑' n : ℕ, x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) :=
        Real.sinh_eq_tsum x
    _ = x * ∑' n : ℕ, x ^ (2 * n) / ((2 * n + 1).factorial : ℝ) := by
        rw [← tsum_mul_left]
        congr 1
        ext n
        rw [show x ^ (2 * n + 1) = x * x ^ (2 * n) by ring_nf]
        ring
    _ ≤ x * ∑' n : ℕ, (x ^ 2 / 6) ^ n := by
        refine mul_le_mul_of_nonneg_left ?_ hx.le
        exact hsumm2.tsum_le_tsum hterm hgeom
    _ = x * (1 - x ^ 2 / 6)⁻¹ := by rw [tsum_geometric_of_lt_one hr0 hr1]
    _ = x / (1 - x ^ 2 / 6) := by field_simp

theorem solution : ∀ x : ℝ, 0 < x →
    1 / x ^ 2 - 1 / 3 < 1 / Real.sinh x ^ 2 ∧ 1 / Real.sinh x ^ 2 < 1 / x ^ 2 := by
  intro x hx
  have hsinh : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have hx2 : 0 < x ^ 2 := by positivity
  have hsinh2 : 0 < Real.sinh x ^ 2 := by positivity
  have hxs : x < Real.sinh x := Real.self_lt_sinh_iff.mpr hx
  constructor
  · rcases le_or_gt 3 (x ^ 2) with h3 | h3
    · have h13 : 1 / x ^ 2 ≤ 1 / 3 :=
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) h3
      have hpos : 0 < 1 / Real.sinh x ^ 2 := by positivity
      linarith
    · have h6 : x ^ 2 < 6 := by nlinarith
      have hb := sinh_le_div x hx h6
      have hpos : 0 < 1 - x ^ 2 / 6 := by nlinarith
      have hsq : Real.sinh x ^ 2 ≤ (x / (1 - x ^ 2 / 6)) ^ 2 :=
        pow_le_pow_left₀ hsinh.le hb 2
      have h2 : 1 / (x / (1 - x ^ 2 / 6)) ^ 2 ≤ 1 / Real.sinh x ^ 2 :=
        one_div_le_one_div_of_le hsinh2 hsq
      have h3' : 1 / (x / (1 - x ^ 2 / 6)) ^ 2 = (1 - x ^ 2 / 6) ^ 2 / x ^ 2 := by
        have hxne : x ≠ 0 := ne_of_gt hx
        field_simp
      have hstep : 1 / x ^ 2 - 1 / 3 < (1 - x ^ 2 / 6) ^ 2 / x ^ 2 := by
        have hx2ne : x ^ 2 ≠ 0 := ne_of_gt hx2
        field_simp
        nlinarith [sq_pos_of_pos hx2]
      linarith
  · have h2 : x ^ 2 < Real.sinh x ^ 2 := by
      have h := pow_lt_pow_left₀ (n := 2) hxs hx.le (by norm_num)
      simpa using h
    exact one_div_lt_one_div_of_lt hx2 h2
