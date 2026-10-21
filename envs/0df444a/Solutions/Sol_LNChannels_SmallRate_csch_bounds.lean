-- Prove2me | solution 1 for LNChannels.SmallRate.csch_bounds
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:14:50.383225+00:00
-- url     : https://prove2.me/submissions/a8fc1a88-6b65-4ae9-9638-edf899371f8d

import Mathlib

set_option autoImplicit false

open scoped Nat

lemma csch_fact_ge (n : ℕ) : 2 * 12 ^ n ≤ (2 * (n + 1))! := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h : (2 * (k + 1 + 1))! = (2 * k + 4) * ((2 * k + 3) * (2 * (k + 1))!) := by
      have : 2 * (k + 1 + 1) = (2 * (k + 1)) + 1 + 1 := by ring
      rw [this, Nat.factorial_succ, Nat.factorial_succ]; ring
    rw [h, pow_succ]
    have h12 : 12 ≤ (2 * k + 4) * (2 * k + 3) := by nlinarith
    calc 2 * (12 ^ k * 12) = (2 * 12 ^ k) * 12 := by ring
      _ ≤ (2 * (k + 1))! * ((2 * k + 4) * (2 * k + 3)) := Nat.mul_le_mul ih h12
      _ = _ := by ring

lemma csch_cosh_lt (x : ℝ) (hx : 0 < x) (hx3 : x ^ 2 < 3) :
    Real.cosh (2 * x) - 1 < 2 * x ^ 2 * (1 - x ^ 2 / 3)⁻¹ := by
  have h1 := Real.hasSum_cosh (2 * x)
  have h2 : HasSum (fun n : ℕ => (2 * x) ^ (2 * (n + 1)) / ((2 * (n + 1))! : ℝ))
      (Real.cosh (2 * x) - 1) := by
    have := (hasSum_nat_add_iff' 1).mpr h1
    simpa using this
  have hr0 : 0 ≤ x ^ 2 / 3 := by positivity
  have hr1 : x ^ 2 / 3 < 1 := by linarith
  have h3 : HasSum (fun n : ℕ => 2 * x ^ 2 * (x ^ 2 / 3) ^ n) (2 * x ^ 2 * (1 - x ^ 2 / 3)⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 hr1).mul_left (2 * x ^ 2)
  have hterm : ∀ n : ℕ, (2 * x) ^ (2 * (n + 1)) / ((2 * (n + 1))! : ℝ)
      ≤ 2 * x ^ 2 * (x ^ 2 / 3) ^ n := by
    intro n
    have hf : (0 : ℝ) < ((2 * (n + 1))! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hge : (2 : ℝ) * 12 ^ n ≤ ((2 * (n + 1))! : ℝ) := by exact_mod_cast csch_fact_ge n
    rw [div_le_iff₀ hf]
    have e : (2 * x) ^ (2 * (n + 1)) = 2 * x ^ 2 * (x ^ 2 / 3) ^ n * (2 * 12 ^ n) := by
      have h4 : (x ^ 2 / 3 * 12) = 4 * x ^ 2 := by ring
      calc (2 * x) ^ (2 * (n + 1)) = 4 * x ^ 2 * (4 * x ^ 2) ^ n := by
            rw [pow_mul, show (2 * x) ^ 2 = 4 * x ^ 2 by ring, pow_succ]; ring
        _ = 4 * x ^ 2 * ((x ^ 2 / 3) * 12) ^ n := by rw [h4]
        _ = _ := by rw [mul_pow]; ring
    rw [e]
    have : 0 ≤ 2 * x ^ 2 * (x ^ 2 / 3) ^ n := by positivity
    exact mul_le_mul_of_nonneg_left hge this
  have hstrict : (2 * x) ^ (2 * (2 + 1)) / ((2 * (2 + 1))! : ℝ)
      < 2 * x ^ 2 * (x ^ 2 / 3) ^ 2 := by
    have e : (2 * x) ^ (2 * (2 + 1)) = 64 * x ^ 6 := by ring
    rw [e]
    have : ((2 * (2 + 1))! : ℝ) = 720 := by norm_num [Nat.factorial]
    rw [this]
    have : 0 < x ^ 6 := by positivity
    have e2 : 2 * x ^ 2 * (x ^ 2 / 3) ^ 2 = 2 * x ^ 6 / 9 := by ring
    rw [e2, div_lt_div_iff₀ (by norm_num) (by norm_num)]
    nlinarith
  exact hasSum_lt hterm hstrict h2 h3

theorem solution (x : ℝ) (hx : 0 < x) :
    1 / x ^ 2 - 1 / 3 < 1 / Real.sinh x ^ 2 ∧
      1 / Real.sinh x ^ 2 < 1 / x ^ 2 := by
  have hs : x < Real.sinh x := Real.self_lt_sinh_iff.mpr hx
  have hsp : 0 < Real.sinh x := by linarith
  constructor
  · have hs2 : 0 < Real.sinh x ^ 2 := by positivity
    have hx2 : 0 < x ^ 2 := by positivity
    by_cases h3 : x ^ 2 < 3
    · have hc := csch_cosh_lt x hx h3
      have hcs : Real.cosh (2 * x) = 1 + 2 * Real.sinh x ^ 2 := by
        rw [Real.cosh_two_mul, Real.cosh_sq]; ring
      rw [hcs] at hc
      have hpos : 0 < 1 - x ^ 2 / 3 := by linarith
      have hlt : Real.sinh x ^ 2 * (1 - x ^ 2 / 3) < x ^ 2 := by
        have : Real.sinh x ^ 2 < x ^ 2 * (1 - x ^ 2 / 3)⁻¹ := by linarith
        calc Real.sinh x ^ 2 * (1 - x ^ 2 / 3) < x ^ 2 * (1 - x ^ 2 / 3)⁻¹ * (1 - x ^ 2 / 3) :=
              mul_lt_mul_of_pos_right this hpos
          _ = x ^ 2 := by rw [mul_assoc, inv_mul_cancel₀ hpos.ne', mul_one]
      have e : 1 / x ^ 2 - 1 / 3 = (1 - x ^ 2 / 3) / x ^ 2 := by field_simp
      rw [e, div_lt_div_iff₀ hx2 hs2]
      linarith
    · have : 1 / x ^ 2 ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) (not_lt.mp h3)
      have : 0 < 1 / Real.sinh x ^ 2 := by positivity
      linarith
  · apply one_div_lt_one_div_of_lt (by positivity)
    exact pow_lt_pow_left₀ hs hx.le (by norm_num)
