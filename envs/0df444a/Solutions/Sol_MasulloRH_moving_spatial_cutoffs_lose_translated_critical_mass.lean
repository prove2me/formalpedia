-- Prove2me | solution 1 for MasulloRH.moving_spatial_cutoffs_lose_translated_critical_mass
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T07:09:18.835321+00:00
-- url     : https://prove2.me/submissions/e11ab94a-e76c-40a0-b9c8-564fa37c233d

import Mathlib
open Filter Topology MeasureTheory
private noncomputable def winW (x : ℝ) := Real.exp |x| * (1+x^2)^2
private noncomputable def winB (R d : ℝ) := Real.exp (-d) * (1+R^2)/(1+d^2)
private theorem win_bound (R d y : ℝ) (hR : 0 ≤ R) (hd : 0 ≤ d)
    (hy : |y+(R+d)| ≤ R) :
    winW (y+(R+d)) / Real.exp (R+d) ≤ (winB R d)^2 * winW y := by
  have hy' : y ≤ -d := by linarith [le_abs_self (y+(R+d))]
  have hdy : d ≤ |y| := by rw [abs_of_nonpos (by linarith : y ≤ 0)]; linarith
  have hsq : (y+(R+d))^2 ≤ R^2 := by nlinarith [sq_abs (y+(R+d)),mul_nonneg (sub_nonneg.mpr hy) (by positivity : 0 ≤ R + |y+(R+d)|)]
  have hsq' : d^2 ≤ y^2 := by nlinarith [sq_abs y,mul_nonneg (sub_nonneg.mpr hdy) (by positivity : 0 ≤ |y|+d)]
  have he : Real.exp |y+(R+d)| ≤ Real.exp ((-d)+(-d)+(R+d)+|y|) :=
    Real.exp_le_exp.mpr (by linarith)
  have hp : (1+(y+(R+d))^2)^2 * (1+d^2)^2 ≤ (1+R^2)^2 * (1+y^2)^2 :=
    mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith : 1+(y+(R+d))^2 ≤ 1+R^2) 2)
      (pow_le_pow_left₀ (by positivity) (by linarith : 1+d^2 ≤ 1+y^2) 2) (by positivity) (by positivity)
  have hh := mul_le_mul he hp (by positivity) (by positivity)
  rw [Real.exp_add, Real.exp_add, Real.exp_add] at hh
  dsimp [winW,winB]
  field_simp
  <;> nlinarith only [hh]
theorem solution (R d : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n) (hd : ∀ n, 0 ≤ d n)
    (hes : Tendsto d atTop atTop) (C : ℝ) (hC : ∀ n,
      Real.exp (-d n) * (1+(R n)^2)/(1+(d n)^2) ≤ C)
    (g : ℝ → ℝ) (hg : AEStronglyMeasurable g volume)
    (hint : Integrable (fun y : ℝ => (Real.exp |y| * (1+y^2)^2) * |g y|)) :
    Tendsto (fun n => ∫ y : ℝ, if |y+(R n+d n)| ≤ R n then
      ((Real.exp |y+(R n+d n)| * (1+(y+(R n+d n))^2)^2) / Real.exp (R n+d n)) * g y
      else 0) atTop (𝓝 0) := by
  let F := fun (n : ℕ) (y : ℝ) => if |y+(R n+d n)| ≤ R n then
    winW (y+(R n+d n)) / Real.exp (R n+d n) * g y else 0
  change Tendsto (fun n => ∫ y : ℝ, F n y) atTop (𝓝 0)
  have ht : Tendsto (fun n => ∫ y : ℝ, F n y) atTop (𝓝 (∫ _ : ℝ, (0:ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun y => C^2 * (winW y * |g y|))
    · apply Eventually.of_forall
      intro n
      have hms : MeasurableSet {y : ℝ | |y+(R n+d n)| ≤ R n} :=
        isClosed_le (by fun_prop) continuous_const |>.measurableSet
      have hcont : Continuous (fun y : ℝ => winW (y+(R n+d n)) / Real.exp (R n+d n)) := by
        dsimp [winW]; fun_prop
      exact (hcont.aestronglyMeasurable.mul hg).indicator hms
    · apply Eventually.of_forall
      intro n
      apply Eventually.of_forall
      intro y
      have h0 : 0 ≤ winW y := by dsimp [winW]; positivity
      by_cases hy : |y+(R n+d n)| ≤ R n
      · simp only [F, if_pos hy, Real.norm_eq_abs, abs_mul]
        rw [abs_of_nonneg (by dsimp [winW]; positivity : 0 ≤ winW (y+(R n+d n))/Real.exp (R n+d n)), ← mul_assoc]
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        exact (win_bound _ _ _ (hR n) (hd n) hy).trans
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (hC n) 2) h0)
      · simp only [F, if_neg hy, norm_zero]; positivity
    · exact hint.const_mul (C^2)
    · apply Eventually.of_forall
      intro y
      apply tendsto_const_nhds.congr'
      filter_upwards [hes.eventually (eventually_gt_atTop (-y))] with n hn
      have hh : ¬ |y+(R n+d n)| ≤ R n := by linarith [le_abs_self (y+(R n+d n))]
      simp [F,hh]
  simpa using ht
