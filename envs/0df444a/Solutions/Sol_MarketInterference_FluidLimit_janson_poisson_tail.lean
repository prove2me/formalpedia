-- Prove2me | solution 1 for MarketInterference.FluidLimit.janson_poisson_tail
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:50:11.829843+00:00
-- url     : https://prove2.me/submissions/ac40f913-83c1-4bbe-85cf-8c0acb9fdcb5

import Mathlib

namespace Aux_Janson_tail
open MeasureTheory ProbabilityTheory NNReal

theorem log7 : (13 : ℝ) / 7 < Real.log 7 := by
  have h1 : Real.exp 13 < 7 ^ 7 := by
    have := Real.exp_one_lt_d9
    have h : Real.exp 13 = Real.exp 1 ^ 13 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h]
    calc Real.exp 1 ^ 13 < (2.7182818286 : ℝ) ^ 13 :=
          pow_lt_pow_left₀ this (Real.exp_pos 1).le (by norm_num)
      _ < 7 ^ 7 := by norm_num
  have h2 : (13 : ℝ) < Real.log (7 ^ 7) := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]; exact h1
  rw [Real.log_pow] at h2
  push_cast at h2
  linarith

theorem key_ineq (r : ℝ) (hr : 7 ≤ r) : 2 - 1 / r ≤ Real.log r := by
  have hr0 : 0 < r := by linarith
  have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < r / 7 by positivity)
  rw [Real.log_div hr0.ne' (by norm_num)] at h1
  have h2 := log7
  have h3 : (r / 7)⁻¹ = 7 / r := by rw [inv_div]
  rw [h3] at h1
  have h4 : 6 / r ≤ 6 / 7 := by
    rw [div_le_div_iff₀ hr0 (by norm_num)]; linarith
  have h5 : 1 - 7 / r = 1 - 1 / r - 6 / r := by ring
  linarith

end Aux_Janson_tail

open MeasureTheory ProbabilityTheory NNReal Aux_Janson_tail in
theorem solution (l0 : ℝ≥0) (t : ℝ) (ht : 7 * (l0 : ℝ) ≤ t) :
    (poissonMeasure l0).real {n : ℕ | t ≤ (n : ℝ)} ≤ Real.exp (-t) := by
  by_cases ht0 : t ≤ 0
  · calc (poissonMeasure l0).real {n : ℕ | t ≤ (n : ℝ)} ≤ 1 := measureReal_le_one
      _ ≤ Real.exp (-t) := Real.one_le_exp (by linarith)
  push_neg at ht0
  set S := {n : ℕ | t ≤ (n : ℝ)} with hS
  have hSm : MeasurableSet S := MeasurableSet.of_discrete
  have hint : Integrable (S.indicator (1 : ℕ → ℝ)) (poissonMeasure l0) :=
    (integrable_const (1 : ℝ)).indicator hSm
  have hsum := hasSum_integral_poissonMeasure hint
  rw [integral_indicator_one hSm] at hsum
  simp only [smul_eq_mul] at hsum
  by_cases hl : (l0 : ℝ) = 0
  · have hzero : ∀ n, Real.exp (-(l0 : ℝ)) * (l0 : ℝ) ^ n / (n.factorial : ℝ) * S.indicator 1 n = 0 := by
      intro n
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h
        have : (0 : ℕ) ∉ S := by simp [hS]; linarith
        simp [Set.indicator_of_notMem this]
      · rw [hl, zero_pow h.ne']; simp
    have hf : (fun n => Real.exp (-(l0 : ℝ)) * (l0 : ℝ) ^ n / (n.factorial : ℝ) * S.indicator 1 n)
        = fun _ => 0 := funext hzero
    rw [hf] at hsum
    rw [hsum.unique hasSum_zero]
    positivity
  · have hl0 : 0 < (l0 : ℝ) := lt_of_le_of_ne l0.2 (Ne.symm hl)
    set lam := (l0 : ℝ) with hlam
    set r := t / lam with hr
    have hr7 : 7 ≤ r := by rw [hr, le_div_iff₀ hl0]; linarith
    have hr0 : 0 < r := by linarith
    have htr : t = lam * r := by rw [hr]; field_simp
    have hq := hasSum_one_poissonMeasure (⟨t, ht0.le⟩ : ℝ≥0)
    try simp only [NNReal.coe_mk] at hq
    set B := Real.exp (t - lam) / r ^ t with hB
    have hbound : ∀ n : ℕ, Real.exp (-lam) * lam ^ n / (n.factorial : ℝ) * S.indicator 1 n ≤
        B * (Real.exp (-t) * t ^ n / (n.factorial : ℝ)) := by
      intro n
      have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
      by_cases hn : n ∈ S
      · rw [Set.indicator_of_mem hn, Pi.one_apply, mul_one]
        have hrt : r ^ t ≤ r ^ (n : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) hn
        rw [Real.rpow_natCast] at hrt
        have hrtpos : 0 < r ^ t := Real.rpow_pos_of_pos hr0 t
        have htn : t ^ n = lam ^ n * r ^ n := by rw [← mul_pow, ← htr]
        have hexp : Real.exp (t - lam) * Real.exp (-t) = Real.exp (-lam) := by
          rw [← Real.exp_add]; ring_nf
        have e1 : B * (Real.exp (-t) * t ^ n / (n.factorial : ℝ)) =
            (Real.exp (-lam) * lam ^ n / (n.factorial : ℝ)) * (r ^ n / r ^ t) := by
          rw [hB, htn, ← hexp]; field_simp
        rw [e1]
        apply le_mul_of_one_le_right (by positivity)
        rw [le_div_iff₀ hrtpos, one_mul]; exact hrt
      · rw [Set.indicator_of_notMem hn, mul_zero]
        have : 0 ≤ B := by rw [hB]; positivity
        positivity
    have hle := hasSum_le hbound hsum (hq.mul_left B)
    rw [mul_one] at hle
    refine hle.trans ?_
    rw [hB, Real.rpow_def_of_pos hr0, ← Real.exp_sub, Real.exp_le_exp]
    have hk := key_ineq r hr7
    have hlr : lam = t / r := by rw [hr]; field_simp
    have : t * (2 - 1 / r) ≤ t * Real.log r := mul_le_mul_of_nonneg_left hk ht0.le
    have e2 : t * (2 - 1 / r) = 2 * t - lam := by rw [hlr]; field_simp
    nlinarith

