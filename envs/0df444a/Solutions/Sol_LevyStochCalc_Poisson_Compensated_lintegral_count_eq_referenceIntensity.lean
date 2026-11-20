-- Prove2me | solution 1 for LevyStochCalc.Poisson.Compensated.lintegral_count_eq_referenceIntensity
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T13:59:40.414394+00:00
-- url     : https://prove2.me/submissions/3905c8f1-e2c6-4603-8ead-aeadb5467c8a

import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometry_F001

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

lemma pois_mean (r : ℝ≥0) : ∑' n : ℕ, (n : ℝ≥0∞) * poissonMeasure r {n} = r := by
  simp_rw [poissonMeasure_singleton]
  have hq : ∀ n : ℕ, 0 ≤ Real.exp (-r) * r ^ n / n.factorial := fun n => by positivity
  have hs : HasSum (fun n : ℕ => (n : ℝ) * (Real.exp (-r) * r ^ n / n.factorial)) r := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [range_one, sum_singleton, Nat.cast_zero, zero_mul, sub_zero]
    have := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
    rw [mul_one] at this
    convert this using 1
    all_goals try rfl
    funext n
    rw [Nat.factorial_succ]; push_cast
    field_simp
    ring
  have : ∀ n : ℕ, (n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-r) * r ^ n / n.factorial) =
      ENNReal.ofReal ((n : ℝ) * (Real.exp (-r) * r ^ n / n.factorial)) := by
    intro n; rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  simp_rw [this]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by have := hq n; positivity) hs.summable, hs.tsum_eq]
  simp

theorem solution {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B)
    (h_finite : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤) :
    ∫⁻ ω, N.N ω B ∂P = LevyStochCalc.Poisson.referenceIntensity ν B := by
  have hm := N.measurable_eval hB
  have hc : Measurable (fun n : ℕ => (n : ℝ≥0∞)) := measurable_of_countable _
  have h1 : ∫⁻ ω, N.N ω B ∂P = ∫⁻ x, x ∂(P.map (fun ω => N.N ω B)) :=
    (lintegral_map measurable_id hm).symm
  rw [h1, N.poisson_law hB h_finite, LevyStochCalc.Poisson.poissonMeasureENN,
    lintegral_map (f := fun x : ℝ≥0∞ => x) measurable_id hc, lintegral_countable', pois_mean,
    ENNReal.coe_toNNReal h_finite]
