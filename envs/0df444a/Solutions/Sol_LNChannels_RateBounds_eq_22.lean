-- Prove2me | solution 1 for LNChannels.RateBounds.eq_22
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:14:07.037206+00:00
-- url     : https://prove2.me/submissions/b9bc7ca6-76c2-46aa-b459-9c27a75e783c

import Mathlib
set_option autoImplicit false
open Real

lemma fE3_fact (m : ℕ) : 5040 * m.factorial ≤ (m + 7).factorial := by
  induction m with
  | zero => simp [Nat.factorial]
  | succ m ih =>
    have h1 : (m + 1 + 7).factorial = (m + 8) * (m + 7).factorial := by
      rw [show m + 1 + 7 = (m + 7) + 1 by ring, Nat.factorial_succ]
    rw [h1, Nat.factorial_succ]
    calc 5040 * ((m + 1) * m.factorial) = (m + 1) * (5040 * m.factorial) := by ring
      _ ≤ (m + 8) * (m + 7).factorial := Nat.mul_le_mul (by omega) ih

lemma fE3_sinh_le (x : ℝ) (hx : 0 ≤ x) :
    sinh x ≤ x + x ^ 3 / 6 + x ^ 5 / 120 + x ^ 7 / 5040 * cosh x := by
  have h1 := Real.hasSum_sinh x
  have h2 := (hasSum_nat_add_iff' 3).mpr h1
  have h3 := (Real.hasSum_cosh x).mul_left (x ^ 7 / 5040)
  have hle := hasSum_le (fun n => ?_) h2 h3
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hle
    norm_num [Nat.factorial] at hle
    linarith
  · have e : 2 * (n + 3) + 1 = 2 * n + 7 := by ring
    simp only [e]
    have hf : (5040 : ℝ) * ((2 * n).factorial : ℝ) ≤ ((2 * n + 7).factorial : ℝ) := by
      exact_mod_cast fE3_fact (2 * n)
    have hpos : (0 : ℝ) < ((2 * n).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hx2 : 0 ≤ x ^ (2 * n + 7) := by positivity
    calc x ^ (2 * n + 7) / ((2 * n + 7).factorial : ℝ)
        ≤ x ^ (2 * n + 7) / (5040 * ((2 * n).factorial : ℝ)) :=
          div_le_div_of_nonneg_left hx2 (by positivity) hf
      _ = x ^ 7 / 5040 * (x ^ (2 * n) / ((2 * n).factorial : ℝ)) := by
          rw [pow_add]; field_simp

lemma fE3_cosh_le (x : ℝ) (hx : 0 ≤ x) (hx2 : x ≤ 2) : cosh x ≤ 4.2 := by
  rw [Real.cosh_eq]
  have h1 : Real.exp x ≤ Real.exp 2 := Real.exp_le_exp.2 hx2
  have h2 : Real.exp (-x) ≤ 1 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by linarith)
  have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have h4 := Real.exp_one_lt_d9
  have h5 : 0 < Real.exp 1 := Real.exp_pos 1
  nlinarith

theorem solution :
    (∀ κ B C m : ℝ, 0 < κ → 0 < m →
      2 * m + 2 * B * Real.exp κ ^ m / (Real.exp κ ^ m - 1) ^ 2
          - 2 * C * Real.exp κ / (Real.exp κ - 1) ^ 2 =
        2 * m + B / 2 / Real.sinh (κ * m / 2) ^ 2 - C / 2 / Real.sinh (κ / 2) ^ 2) ∧
    ∀ x : ℝ, 0 < x →
      1 / x ^ 2 - 1 / 3 < 1 / Real.sinh x ^ 2 ∧ 1 / Real.sinh x ^ 2 < 1 / x ^ 2 := by
  have alg : ∀ u : ℝ, 1 < u → 2 * u ^ 2 / (u ^ 2 - 1) ^ 2 = 1 / 2 / ((u - u⁻¹) / 2) ^ 2 := by
    intro u hu1
    have hne : u ≠ 0 := by positivity
    have hne2 : u ^ 2 - 1 ≠ 0 := by nlinarith
    have hne3 : u - u⁻¹ ≠ 0 := by
      intro h
      have : u * (u - u⁻¹) = 0 := by rw [h]; ring
      rw [mul_sub, mul_inv_cancel₀ hne] at this
      nlinarith
    field_simp
  have ident : ∀ a : ℝ, 0 < a → 2 * Real.exp a / (Real.exp a - 1) ^ 2 = 1 / 2 / Real.sinh (a / 2) ^ 2 := by
    intro a ha
    have hu : Real.exp a = Real.exp (a / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hu1 : 1 < Real.exp (a / 2) := by
      have := Real.add_one_lt_exp (show a / 2 ≠ 0 by positivity)
      linarith
    have hs : Real.sinh (a / 2) = (Real.exp (a / 2) - (Real.exp (a / 2))⁻¹) / 2 := by
      rw [Real.sinh_eq, Real.exp_neg]
    rw [hu, hs]
    exact alg _ hu1
  refine ⟨?_, ?_⟩
  · intro κ B C m hκ hm
    have e1 : Real.exp κ ^ m = Real.exp (κ * m) := by rw [← Real.exp_mul]
    have i1 := ident (κ * m) (by positivity)
    have i2 := ident κ hκ
    rw [e1]
    have : 2 * B * Real.exp (κ * m) / (Real.exp (κ * m) - 1) ^ 2 =
        B * (2 * Real.exp (κ * m) / (Real.exp (κ * m) - 1) ^ 2) := by ring
    have : 2 * C * Real.exp κ / (Real.exp κ - 1) ^ 2 =
        C * (2 * Real.exp κ / (Real.exp κ - 1) ^ 2) := by ring
    rw [this, i2]
    have h2 : 2 * B * Real.exp (κ * m) / (Real.exp (κ * m) - 1) ^ 2 =
        B * (2 * Real.exp (κ * m) / (Real.exp (κ * m) - 1) ^ 2) := by ring
    rw [h2, i1]
    ring
  · intro x hx
    have hs : x < Real.sinh x := Real.self_lt_sinh_iff.2 hx
    have hs0 : 0 < Real.sinh x := by linarith
    constructor
    · by_cases h3 : 3 ≤ x ^ 2
      · have : 1 / x ^ 2 ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) h3
        have : 0 < 1 / Real.sinh x ^ 2 := by positivity
        linarith
      · push_neg at h3
        have hx2 : x ≤ 2 := by nlinarith
        have hsl := fE3_sinh_le x hx.le
        have hc := fE3_cosh_le x hx.le hx2
        have hx7 : 0 ≤ x ^ 7 := by positivity
        have hb : Real.sinh x ≤ x + x ^ 3 / 6 + x ^ 5 / 120 + x ^ 7 / 1200 := by
          have : x ^ 7 / 5040 * cosh x ≤ x ^ 7 / 5040 * 4.2 :=
            mul_le_mul_of_nonneg_left hc (by positivity)
          linarith
        have hR : Real.sinh x ^ 2 ≤ (x + x ^ 3 / 6 + x ^ 5 / 120 + x ^ 7 / 1200) ^ 2 :=
          pow_le_pow_left₀ hs0.le hb 2
        set t := x ^ 2 with ht
        have ht0 : 0 < t := by positivity
        have hQ : (x + x ^ 3 / 6 + x ^ 5 / 120 + x ^ 7 / 1200) ^ 2 =
            t * (1 + t / 6 + t ^ 2 / 120 + t ^ 3 / 1200) ^ 2 := by
          rw [ht]; ring
        have hP : 3 - (3 - t) * (1 + t / 6 + t ^ 2 / 120 + t ^ 3 / 1200) ^ 2 =
            t ^ 2 * (t ^ 5 + 17 * t ^ 4 + 440 * t ^ 3 + 4900 * t ^ 2 + 44800 * t + 288000) / 1440000 := by
          ring
        have hPpos : 0 < 3 - (3 - t) * (1 + t / 6 + t ^ 2 / 120 + t ^ 3 / 1200) ^ 2 := by
          rw [hP]; positivity
        have h3t : 0 < 3 - t := by linarith
        have key : (3 - t) * Real.sinh x ^ 2 < 3 * t := by
          calc (3 - t) * Real.sinh x ^ 2 ≤ (3 - t) * (t * (1 + t / 6 + t ^ 2 / 120 + t ^ 3 / 1200) ^ 2) := by
                rw [← hQ]; exact mul_le_mul_of_nonneg_left hR h3t.le
            _ < 3 * t := by nlinarith [mul_pos ht0 hPpos]
        have e : 1 / x ^ 2 - 1 / 3 = (3 - t) / (3 * t) := by
          rw [ht]; field_simp
        rw [e, div_lt_div_iff₀ (by positivity) (by positivity)]
        nlinarith [key]
    · have h1 : x ^ 2 < Real.sinh x ^ 2 := pow_lt_pow_left₀ hs hx.le (by norm_num)
      exact one_div_lt_one_div_of_lt (by positivity) h1
