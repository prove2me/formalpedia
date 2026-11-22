-- Prove2me | solution 1 for MasulloRH.critical_weight_negative_shell_mass_of_euler_mesh
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T14:34:41.659169+00:00
-- url     : https://prove2.me/submissions/f604f655-f9c1-4c6d-b5fb-8aab287f6aca

import Mathlib
open MeasureTheory Set
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (a R : ℝ) (ha : 0 < a)
    (hR : 0 ≤ R)
    (hd : (∫ x : ℝ, (if x < 0 then (-1:ℝ) else 1) + 4*x/(1+x^2) ∂μ) = -1)
    (hm : (∫ x : ℝ, (if x < 0 then 1/(1+x^2)^2 else 0) ∂μ) ≤ a^4) :
    μ.real (Ici (-R)) ≤ 2*a + (1+R^2)^2 * a^4 := by
  let d : ℝ → ℝ := fun x => (if x < 0 then (-1:ℝ) else 1) + 4*x/(1+x^2)
  let e : ℝ → ℝ := fun x => if x < 0 then 1/(1+x^2)^2 else 0
  let b : ℝ := (1+R^2)^2 + 1/(2*a^3)
  have hm1 (x : ℝ) : 0 ≤ e x ∧ e x ≤ 1 := by
    dsimp [e]
    split_ifs
    · constructor
      · positivity
      · apply (div_le_one (by positivity)).2
        nlinarith [sq_nonneg x, sq_nonneg (x^2)]
    · norm_num
  have de : Integrable d μ := by
    apply (integrable_const (μ := μ) (3:ℝ)).mono'
    · apply Measurable.aestronglyMeasurable
      exact (Measurable.ite measurableSet_Iio measurable_const measurable_const).add
        (by fun_prop : Measurable (fun x : ℝ => 4*x/(1+x^2)))
    · filter_upwards with x
      have hx : |4*x/(1+x^2)| ≤ 2 := by
        rw [abs_le]; constructor
        · apply (le_div_iff₀ (by positivity)).2; nlinarith [sq_nonneg (x+1)]
        · apply (div_le_iff₀ (by positivity)).2; nlinarith [sq_nonneg (x-1)]
      dsimp [d]
      have hsign : |(if x < 0 then (-1:ℝ) else 1)| = 1 := by split_ifs <;> norm_num
      linarith [abs_add_le (if x < 0 then (-1:ℝ) else 1) (4*x/(1+x^2))]
  have ee : Integrable e μ := by
    apply (integrable_const (μ := μ) (1:ℝ)).mono'
    · exact (Measurable.ite measurableSet_Iio (by fun_prop) measurable_const).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (hm1 x).1]
      exact (hm1 x).2
  let j : ℝ → ℝ := (Ici (-R)).indicator (fun _ => (1:ℝ))
  have hj : Integrable j μ := (integrable_const (1:ℝ)).indicator measurableSet_Ici
  have hjval : (∫ x, j x ∂μ) = μ.real (Ici (-R)) := by simp [j, integral_indicator, measurableSet_Ici]
  have hr : Integrable (fun x => (1/2:ℝ)*(d x+1) + b*e x + 3*a/2) μ :=
    (((de.add (integrable_const _)).const_mul _).add (ee.const_mul _)).add (integrable_const _)
  have point (x : ℝ) : j x ≤ (1/2:ℝ)*(d x+1) + b*e x + 3*a/2 := by
    by_cases hx : x < 0
    · let z : ℝ := -x/(1+x^2)
      have hz : 0 ≤ z := div_nonneg (neg_nonneg.mpr hx.le) (by positivity)
      have hp : z^4 ≤ e x := by
        dsimp [z,e]; simp only [if_pos hx, div_pow]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg x, sq_nonneg (x^2), sq_nonneg (x^3), sq_nonneg (x^4)]
      have hY : 4*a^3*z ≤ e x+3*a^4 := by
        nlinarith [mul_nonneg (sq_nonneg (z-a)) (show 0 ≤ z^2+2*a*z+3*a^2 by positivity)]
      have hY' : 2*z ≤ (1/(2*a^3))*e x+3*a/2 := by
        field_simp [ne_of_gt ha]
        nlinarith
      have hj' : j x ≤ (1+R^2)^2*e x := by
        dsimp [j,e]; rw [if_pos hx]
        by_cases hh : x ∈ Ici (-R)
        · rw [indicator_of_mem hh]
          change 1 ≤ _
          rw [mul_one_div, le_div_iff₀ (by positivity)]
          have hxR : -R ≤ x := hh
          have hx2 : x^2 ≤ R^2 := by nlinarith [mul_nonneg (show 0 ≤ R+x by linarith) (show 0 ≤ R-x by linarith)]
          nlinarith [mul_nonneg (sub_nonneg.mpr hx2) (show 0 ≤ 2+x^2+R^2 by positivity)]
        · rw [indicator_of_notMem hh]; positivity
      have hd' : d x+1= -4*z := by dsimp [d,z]; rw [if_pos hx]; ring
      rw [hd']; dsimp [b]; linarith
    · have hx0 : 0 ≤ x := le_of_not_gt hx
      have hh : x ∈ Ici (-R) := by change -R ≤ x; linarith
      simp [j, hh, d,e,hx]
      first | positivity | nlinarith [div_nonneg (show 0 ≤ 4*x by positivity) (show 0 ≤ 1+x^2 by positivity)]
  have hineq := integral_mono hj hr point
  rw [hjval] at hineq
  change (∫ x, d x ∂μ) = -1 at hd
  change (∫ x, e x ∂μ) ≤ a^4 at hm
  have h1 : Integrable (fun x => (1/2:ℝ)*(d x+1)) μ := (de.add (integrable_const (1:ℝ))).const_mul _
  have h2 : Integrable (fun x => b*e x) μ := ee.const_mul _
  have h12 : Integrable (fun x => (1/2:ℝ)*(d x+1)+b*e x) μ := h1.add h2
  rw [integral_add h12 (integrable_const (3*a/2)), integral_add h1 h2,
      integral_const_mul, integral_const_mul, integral_add de (integrable_const (1:ℝ)), hd] at hineq
  simp at hineq
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hfin := mul_le_mul_of_nonneg_left hm hb
  have heq : b*a^4 + 3*a/2 = 2*a + (1+R^2)^2*a^4 := by
    dsimp [b]; field_simp [ne_of_gt ha]; ring
  linarith
