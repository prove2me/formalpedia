-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_drawdown_singleton_split_le
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T01:35:20.418531+00:00
-- url     : https://prove2.me/submissions/dee9c9b5-94b2-41f2-b086-e174e1fb3421

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsupp : μ (Iio (0 : ℝ)) = 0) (x : ℝ) (hx : 0 < x) :
    μ {x} * ENNReal.ofReal (1 - Real.exp (-x)) +
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂μ) ≤ 1 := by
  let c := ENNReal.ofReal (1 - Real.exp (-x))
  let f : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (-1 * y))
  let g := ({x} : Set ℝ).indicator (fun _ => c)
  have hg : Measurable g := measurable_const.indicator (measurableSet_singleton x)
  have hi : ∫⁻ y, g y ∂μ = μ {x} * c := by
    dsimp [g]
    rw [lintegral_indicator (measurableSet_singleton x), lintegral_const]
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, mul_comm]
  change μ {x} * c + (∫⁻ y, f y ∂μ) ≤ 1
  rw [← hi, ← lintegral_add_left hg]
  have hn : ∀ᵐ y ∂μ, 0 ≤ y := by
    rw [ae_iff]
    simpa only [not_le, Set.Iio] using hsupp
  have hb : ∀ᵐ y ∂μ, g y + f y ≤ 1 := by
    filter_upwards [hn] with y hy
    by_cases h : y ∈ ({x} : Set ℝ)
    · have he := Set.mem_singleton_iff.mp h
      subst y
      dsimp [g, f, c]
      rw [Set.indicator_of_mem (Set.mem_singleton x), neg_one_mul, ← ENNReal.ofReal_add]
      · simp
      · have hx' : Real.exp (-x) ≤ 1 := by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
        linarith
      · positivity
    · simp only [g, Set.indicator_of_notMem h, zero_add, f, neg_one_mul]
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ ∫⁻ _ : ℝ, (1 : ℝ≥0∞) ∂μ := lintegral_mono_ae hb
    _ = 1 := by simp
