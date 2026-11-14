-- Prove2me | solution 1 for KSATSingleFlip.Connect.poisson_two_sided_tail
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:45:35.371185+00:00
-- url     : https://prove2.me/submissions/2a2bda75-544b-4489-82d0-5f1b6b7382e0

import Theorems.Thm_ResolvingNRM_IRT_poisson_tail_bound
import Theorems.Thm_StateIndepNRM_eq_12
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem solution (r : ℝ≥0) (hr : 0 < r) (x : ℝ) (hx : 0 < x) :
    (poissonMeasure r).real {k : ℕ | x ≤ |(k:ℝ)-(r:ℝ)|} ≤
      2*Real.exp (-(x^2)/(8*((r:ℝ)+x))) := by
  classical
  have hrr : (0:ℝ) < r := by exact_mod_cast hr
  have hrx : 0 < (r:ℝ)+x := by positivity
  by_cases hxr : x ≤ (r:ℝ)
  · have ht := ResolvingNRM.IRT.poisson_tail_bound (r:ℝ) x hrr hx hxr
    have hevent : (poissonMeasure r).real {k : ℕ | x ≤ |(k:ℝ)-(r:ℝ)|} =
      ∑' k : ℕ, if x ≤ |(k:ℝ)-(r:ℝ)| then ResolvingNRM.IRT.poissonPMF (r:ℝ) k else 0 := by
      rw [← integral_indicator_one (show MeasurableSet {k : ℕ | x ≤ |(k:ℝ)-(r:ℝ)|} by measurability)]
      rw [integral_poissonMeasure]
      congr 1
      funext k
      by_cases hk : x ≤ |(k:ℝ)-(r:ℝ)|
      · simp [Set.indicator_of_mem, hk, ResolvingNRM.IRT.poissonPMF, max_eq_left (le_of_lt hrr), smul_eq_mul]
      · simp [Set.indicator_of_notMem, hk]
    rw [hevent]
    apply le_trans ht
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    have : 0 ≤ x^2 := sq_nonneg x
    have hd : (0:ℝ) < 3*(r:ℝ) := by positivity
    have he : (0:ℝ) < 8*((r:ℝ)+x) := by positivity
    have hdiv : x^2/(8*((r:ℝ)+x)) ≤ x^2/(3*(r:ℝ)) := by
      apply (div_le_div_iff₀ he hd).2
      nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 5*(r:ℝ)+8*x by positivity)]
    simp only [neg_div]
    linarith
  · have hempty : {k : ℕ | x ≤ |(k:ℝ)-(r:ℝ)|} = {k : ℕ | (r:ℝ)+x ≤ (k:ℝ)} := by
      ext k
      simp only [Set.mem_setOf_eq, le_abs]
      have hk : 0 ≤ (k:ℝ) := by positivity
      constructor
      · rintro (h | h) <;> linarith
      · intro h; left; linarith
    rw [hempty]
    have ht := StateIndepNRM.eq_12 r hr x (le_of_lt hx)
    apply le_trans ht
    have he : Real.exp (-(x^2/(2*((r:ℝ)+x)))) ≤ Real.exp (-(x^2/(8*((r:ℝ)+x)))) := by
      apply Real.exp_le_exp.mpr
      have ha : 0 ≤ x^2 := sq_nonneg x
      have hb : 0 < (r:ℝ)+x := by positivity
      have hdiv : x^2/(8*((r:ℝ)+x)) ≤ x^2/(2*((r:ℝ)+x)) := by
        apply (div_le_div_iff₀ (show 0 < 8*((r:ℝ)+x) by positivity) (show 0 < 2*((r:ℝ)+x) by positivity)).2
        nlinarith [mul_nonneg ha (le_of_lt hb)]
      linarith
    have hp : 0 ≤ Real.exp (-(x^2/(8*((r:ℝ)+x)))) := le_of_lt (Real.exp_pos _)
    simp only [neg_div] at he hp ⊢
    linarith
