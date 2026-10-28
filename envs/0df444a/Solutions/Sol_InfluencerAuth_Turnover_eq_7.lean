-- Prove2me | solution 1 for InfluencerAuth.Turnover.eq_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T10:15:23.710899+00:00
-- url     : https://prove2.me/submissions/04e1b5da-1b17-4fb6-8b1b-994238b2fb0a

import Mathlib
import Definitions.Def_InfluencerAuth_Turnover_Model

open MeasureTheory Set Filter Topology InfluencerAuth.Turnover

theorem solution (β r x : ℝ) (hβ : 0 < β) (hr : 0 < r) (hx : 0 < x) (hxβ : x < β) :
    HasDerivAt (authValue β x r)
        (∫ s in Set.Ioi (0 : ℝ), Real.exp (-(r + β - x) * s)) ((β - x) / β) ∧
      ∫ s in Set.Ioi (0 : ℝ), Real.exp (-(r + β - x) * s) = 1 / (r + β - x) := by
  have hk : 0 < β - x := by linarith
  have hint : ∫ s in Set.Ioi (0 : ℝ), Real.exp (-(r + β - x) * s) = 1 / (r + β - x) := by
    rw [integral_exp_mul_Ioi (by linarith) 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp
  refine ⟨?_, hint⟩
  set c0 := β / (β - x) with hc0
  set x0 := (β - x) / β with hx0
  have hc0pos : 0 < c0 := div_pos hβ hk
  have hx0pos : 0 < x0 := div_pos hk hβ
  have hxc : x0 * c0 = 1 := by rw [hx0, hc0]; field_simp
  -- integrand and its derivative
  set F : ℝ → ℝ → ℝ := fun A s =>
    Real.exp (-r * s) / (c0 + ((1 - A * c0) / A) * Real.exp (-(β - x) * s)) with hF
  set F' : ℝ → ℝ → ℝ := fun A s =>
    Real.exp (-r * s) * Real.exp (-(β - x) * s) /
      (A * c0 + (1 - A * c0) * Real.exp (-(β - x) * s)) ^ 2 with hF'
  have hAD : ∀ A s, A ≠ 0 → A * (c0 + ((1 - A * c0) / A) * Real.exp (-(β - x) * s)) =
      A * c0 + (1 - A * c0) * Real.exp (-(β - x) * s) := by
    intro A s hA; field_simp
  -- key lower bound on the ball
  have hlow : ∀ A ∈ Ioo (x0 / 2) (3 * x0 / 2), ∀ s, 0 ≤ s →
      1 / 2 ≤ A * c0 + (1 - A * c0) * Real.exp (-(β - x) * s) := by
    intro A hA s hs
    have he1 : Real.exp (-(β - x) * s) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have he0 := Real.exp_pos (-(β - x) * s)
    have hu : 1 / 2 < A * c0 := by nlinarith [hA.1]
    nlinarith
  have hs : Ioo (x0 / 2) (3 * x0 / 2) ∈ 𝓝 x0 := Ioo_mem_nhds (by linarith) (by linarith)
  have hderiv : ∀ A ∈ Ioo (x0 / 2) (3 * x0 / 2), ∀ s, 0 ≤ s → HasDerivAt (F · s) (F' A s) A := by
    intro A hA s hs0
    have hA0 : A ≠ 0 := by linarith [hA.1]
    have hpos := hlow A hA s hs0
    have hD : c0 + ((1 - A * c0) / A) * Real.exp (-(β - x) * s) ≠ 0 := by
      intro h; have := hAD A s hA0; rw [h, mul_zero] at this; linarith
    have h1 : HasDerivAt (fun A => (1 - A * c0) / A) ((-(1 * c0) * A - (1 - A * c0) * 1) / A ^ 2) A :=
      (((hasDerivAt_id A).mul_const c0).const_sub 1).div (hasDerivAt_id A) hA0
    have h2 := ((h1.mul_const (Real.exp (-(β - x) * s))).const_add c0)
    have h3 := (hasDerivAt_const A (Real.exp (-r * s))).div h2 hD
    refine h3.congr_deriv ?_
    simp only [hF']
    have hD' : A * c0 + (1 - A * c0) * Real.exp (-(β - x) * s) ≠ 0 := by linarith
    rw [← hAD A s hA0]
    field_simp
    ring
  have hmeas : ∀ A, AEStronglyMeasurable (F A) (volume.restrict (Ioi 0)) := fun A =>
    (Measurable.div (by fun_prop) (by fun_prop)).aestronglyMeasurable
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0:ℝ)))
    (F := F) (F' := F') (x₀ := x0) (bound := fun s => 4 * Real.exp (-r * s)) hs
    (Eventually.of_forall hmeas) ?_ ?_ ?_ ?_ ?_
  · have e1 : authValue β x r = fun A => ∫ s in Ioi (0:ℝ), F A s := by
      funext A; rfl
    have hval : ∫ s in Ioi (0:ℝ), F' x0 s = ∫ s in Ioi (0:ℝ), Real.exp (-(r + β - x) * s) := by
      refine setIntegral_congr_fun (measurableSet_Ioi (a := (0:ℝ))) fun s _ => ?_
      simp only [hF']
      rw [hxc, sub_self, zero_mul, add_zero, one_pow, div_one, ← Real.exp_add]
      ring_nf
    rw [e1, ← hval]
    exact hres.2
  · have e : F x0 = fun s => Real.exp (-r * s) / c0 := by
      funext s; simp only [hF]; rw [hxc, sub_self, zero_div, zero_mul, add_zero]
    rw [e]
    exact (exp_neg_integrableOn_Ioi 0 hr).div_const c0
  · exact (Measurable.div (by fun_prop) (by fun_prop)).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun s hs0 => fun A hA => ?_
    have hpos := hlow A hA s (le_of_lt hs0)
    have he1 : Real.exp (-(β - x) * s) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [mem_Ioi.1 hs0])
    have he0 := Real.exp_pos (-(β - x) * s)
    have hr0 := Real.exp_pos (-r * s)
    simp only [hF']
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    have hsq : 1 / 4 ≤ (A * c0 + (1 - A * c0) * Real.exp (-(β - x) * s)) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left he1 hr0.le, mul_le_mul_of_nonneg_left hsq hr0.le]
  · exact Integrable.const_mul (exp_neg_integrableOn_Ioi 0 hr) 4
  · exact ae_restrict_of_forall_mem measurableSet_Ioi fun s hs0 A hA =>
      hderiv A hA s (le_of_lt hs0)
