-- Prove2me | solution 1 for MeanOnlyProphet.lemma_A_7
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:01:39.494453+00:00
-- url     : https://prove2.me/submissions/a940624d-1134-42dc-9bc1-9d588f4bd842

import Mathlib

open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Measurable Z) (x : ℝ) (hx : 0 < x)
    (hZx : ∃ a : ℝ, ∀ᵐ ω ∂P, Z ω ∈ Set.Icc a (a + x)) :
    (∫ ω, Real.exp (Z ω) ∂P) * Real.exp (-∫ ω, Z ω ∂P) ≤ Real.exp x / (1 + x) := by
  obtain ⟨a, ha⟩ := hZx
  have hZi : Integrable Z P := by
    refine Integrable.mono' (integrable_const (|a| + x)) hZ.aestronglyMeasurable ?_
    filter_upwards [ha] with ω hω
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> cases abs_le.mp (le_refl |a|) <;> linarith [hω.1, hω.2, abs_nonneg a]
  have hEi : Integrable (fun ω => Real.exp (Z ω)) P := by
    refine Integrable.mono' (integrable_const (Real.exp (a + x)))
      (Real.measurable_exp.comp hZ).aestronglyMeasurable ?_
    filter_upwards [ha] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr hω.2
  set m := ∫ ω, Z ω ∂P with hm
  have hm1 : a ≤ m := by
    have := integral_mono_ae (integrable_const a) hZi (by filter_upwards [ha] with ω hω; exact hω.1)
    simpa using this
  have hm2 : m ≤ a + x := by
    have := integral_mono_ae hZi (integrable_const (a + x)) (by filter_upwards [ha] with ω hω; exact hω.2)
    simpa using this
  -- chord bound
  have hchord : ∀ z ∈ Set.Icc a (a + x),
      Real.exp z ≤ Real.exp a * ((a + x - z) / x + (z - a) / x * Real.exp x) := by
    intro z hz
    set t := (z - a) / x with ht
    have ht0 : 0 ≤ t := div_nonneg (by linarith [hz.1]) hx.le
    have ht1 : t ≤ 1 := by rw [ht, div_le_one hx]; linarith [hz.2]
    have hzt : z = (1 - t) * a + t * (a + x) := by rw [ht]; field_simp; ring
    have hc := convexOn_exp.2 (Set.mem_univ a) (Set.mem_univ (a + x)) (by linarith : 0 ≤ 1 - t)
      ht0 (by ring)
    simp only [smul_eq_mul] at hc
    rw [hzt]
    calc Real.exp ((1 - t) * a + t * (a + x)) ≤ (1 - t) * Real.exp a + t * Real.exp (a + x) := hc
      _ = _ := by
          rw [Real.exp_add]; field_simp; ring
  have hint : ∫ ω, Real.exp (Z ω) ∂P ≤
      ∫ ω, Real.exp a * ((a + x - Z ω) / x + (Z ω - a) / x * Real.exp x) ∂P := by
    apply integral_mono_ae hEi
    · have h1 : Integrable (fun ω => Real.exp a * ((a + x) / x - Real.exp x * a / x +
          Z ω * ((Real.exp x - 1) / x))) P :=
        ((integrable_const _).add (hZi.mul_const _)).const_mul _
      refine h1.congr (Filter.Eventually.of_forall (fun ω => ?_))
      simp only; field_simp; ring
    · filter_upwards [ha] with ω hω using hchord _ hω
  have hval : ∫ ω, Real.exp a * ((a + x - Z ω) / x + (Z ω - a) / x * Real.exp x) ∂P =
      Real.exp a * ((a + x - m) / x + (m - a) / x * Real.exp x) := by
    have e : (fun ω => Real.exp a * ((a + x - Z ω) / x + (Z ω - a) / x * Real.exp x)) =
        fun ω => Real.exp a * ((a + x) / x - Real.exp x * a / x) +
          Real.exp a * ((Real.exp x - 1) / x) * Z ω := by
      funext ω; field_simp; ring
    rw [e, integral_add (integrable_const _) (hZi.const_mul _), integral_const, integral_const_mul,
      ← hm]
    simp only [probReal_univ, one_smul, smul_eq_mul, one_mul]
    field_simp; ring
  rw [hval] at hint
  set q := (m - a) / x with hq
  have hq0 : 0 ≤ q := div_nonneg (by linarith) hx.le
  have hq1 : q ≤ 1 := by rw [hq, div_le_one hx]; linarith
  have hmq : m = a + q * x := by rw [hq]; field_simp; ring
  have h1q : (a + x - m) / x = 1 - q := by rw [hmq]; field_simp; ring
  rw [h1q] at hint
  -- scalar inequality
  have hlin : (1 + x) * (1 - q + q * Real.exp x) ≤ Real.exp x * (1 + q * x) := by
    have hex := Real.add_one_le_exp x
    nlinarith [mul_nonneg (sub_nonneg.mpr hq1) (sub_nonneg.mpr (by linarith : x + 1 ≤ Real.exp x))]
  have htan : 1 + q * x ≤ Real.exp (q * x) := by linarith [Real.add_one_le_exp (q * x)]
  have hE0 : 0 < Real.exp (-m) := Real.exp_pos _
  calc (∫ ω, Real.exp (Z ω) ∂P) * Real.exp (-m)
      ≤ Real.exp a * (1 - q + q * Real.exp x) * Real.exp (-m) :=
        mul_le_mul_of_nonneg_right hint hE0.le
    _ = (1 - q + q * Real.exp x) * Real.exp (-(q * x)) := by
        rw [hmq, show -(a + q * x) = -a + -(q * x) by ring, Real.exp_add, Real.exp_neg a]
        field_simp
    _ ≤ Real.exp x / (1 + x) := by
        rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by linarith)]
        have : 0 ≤ Real.exp x := (Real.exp_pos x).le
        nlinarith [mul_le_mul_of_nonneg_left htan this]
