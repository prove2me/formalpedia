-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.theorem1_min_increment_secant_formula
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T21:30:36.526605+00:00
-- url     : https://prove2.me/submissions/d090df45-8802-49c7-b440-57653e6a6e9f

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

/-!
Proof source for the proposed secant-identity child of
`theorem1_subdiff_condition_optimal`. Auxiliary bounds for the later base-fare
argument are separate; this candidate contains only the exact integral
identity and its direct supporting rewrite. -/

/-- The level-one expected revenue is the integral of the clamped payoff. -/
theorem expRevenue_one_as_min_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (t : ℝ) :
    expRevenue P X f p 1 t =
      ∫ ω, f 1 * min t (X 1 ω) ∂P := by
  simp only [expRevenue]
  apply integral_congr_ae
  filter_upwards [] with ω
  by_cases ht : t < X 1 ω
  · simp [revenue, ht, min_eq_left (le_of_lt ht)]
  · have hxt : X 1 ω ≤ t := le_of_not_gt ht
    simp [revenue, ht, min_eq_right hxt]

/-- The positive level-one revenue secant is fare times the expected
normalized increment. -/
theorem expRevenue_one_secant_eq_integral_increment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) :
    (expRevenue P X f p 1 (a + h) - expRevenue P X f p 1 a) / h =
      f 1 * ∫ ω, (min (a + h) (X 1 ω) - min a (X 1 ω)) / h ∂P := by
  letI : IsProbabilityMeasure P := hM.isProb
  have hUmeas : Measurable (fun ω => min (a + h) (X 1 ω)) :=
    measurable_const.min (hM.meas 1)
  have hAmeas : Measurable (fun ω => min a (X 1 ω)) :=
    measurable_const.min (hM.meas 1)
  have hUInt : Integrable (fun ω => min (a + h) (X 1 ω)) P := by
    have hs : 0 ≤ a + h := by linarith
    have hmin_nonneg (ω : Ω) : 0 ≤ min (a + h) (X 1 ω) :=
      le_min hs (hM.nonneg 1 ω)
    apply Integrable.of_bound hUmeas.aestronglyMeasurable (a + h)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hmin_nonneg ω)]
    exact min_le_left _ _
  have hAint : Integrable (fun ω => min a (X 1 ω)) P := by
    have hmin_nonneg (ω : Ω) : 0 ≤ min a (X 1 ω) :=
      le_min ha (hM.nonneg 1 ω)
    apply Integrable.of_bound hAmeas.aestronglyMeasurable a
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hmin_nonneg ω)]
    exact min_le_left _ _
  have hqmean :
      ∫ ω, (min (a + h) (X 1 ω) - min a (X 1 ω)) / h ∂P =
        ( (∫ ω, min (a + h) (X 1 ω) ∂P) -
          (∫ ω, min a (X 1 ω) ∂P)) / h := by
    calc
      _ = ∫ ω, h⁻¹ *
          (min (a + h) (X 1 ω) - min a (X 1 ω)) ∂P := by
            apply integral_congr_ae
            filter_upwards [] with ω
            rw [div_eq_mul_inv]
            ring
      _ = h⁻¹ * ((∫ ω, min (a + h) (X 1 ω) ∂P) -
          (∫ ω, min a (X 1 ω) ∂P)) := by
            rw [integral_const_mul, integral_sub hUInt hAint]
      _ = _ := by rw [div_eq_mul_inv]; ring
  rw [expRevenue_one_as_min_integral, expRevenue_one_as_min_integral,
    integral_const_mul, integral_const_mul]
  rw [hqmean]
  ring

/-- Candidate entry point for the source-faithful Theorem 1 reduction. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) :
    (expRevenue P X f p 1 (a + h) - expRevenue P X f p 1 a) / h =
      f 1 * ∫ ω, (min (a + h) (X 1 ω) - min a (X 1 ω)) / h ∂P := by
  exact expRevenue_one_secant_eq_integral_increment P X f p hM ha hh
