-- Prove2me | solution 1 for Kyprianou.Ch03.stableGridLaplaceThresholdNullV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:48:56.069549+00:00
-- url     : https://prove2.me/submissions/135fad54-8fdd-4003-8dac-928fd4587cfb

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n))
    (hnon : ∀ n, 0 ≤ᵐ[P] Y n)
    (hlim : Tendsto (fun n => ∫ w, Real.exp (-Y n w) ∂P) atTop (𝓝 0))
    (m : ℝ) : P (⋂ n : ℕ, {w | Y n w ≤ m}) = 0 := by
  let B : Set Ω := ⋂ n : ℕ, {w | Y n w ≤ m}
  have hB : MeasurableSet B := MeasurableSet.iInter
    (fun n => measurableSet_le (hY n) measurable_const)
  let g : Ω → ℝ := B.indicator (fun _ => Real.exp (-m))
  have hg : Integrable g P := (integrable_indicator_iff hB).mpr (integrable_const _)
  have hle (n : ℕ) : (∫ w, g w ∂P) ≤ ∫ w, Real.exp (-Y n w) ∂P := by
    have hi : Integrable (fun w => Real.exp (-Y n w)) P := by
      apply (integrable_const (1 : ℝ)).mono
      · exact (Real.measurable_exp.comp (hY n).neg).aestronglyMeasurable
      · filter_upwards [hnon n] with w hw
        simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_one]
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hw)
    apply integral_mono_ae hg hi
    filter_upwards with w
    by_cases hb : w ∈ B
    · have h : Y n w ≤ m := Set.mem_iInter.mp hb n
      dsimp [g]; rw [Set.indicator_of_mem hb]
      exact Real.exp_le_exp.mpr (by linarith)
    · dsimp [g]; rw [Set.indicator_of_notMem hb]
      exact (Real.exp_pos _).le
  have hzero : ∫ w, g w ∂P = 0 := by
    have hnn : 0 ≤ᵐ[P] g := Eventually.of_forall fun w => by
      change 0 ≤ g w
      by_cases hb : w ∈ B
      · dsimp [g]; rw [Set.indicator_of_mem hb]; positivity
      · dsimp [g]; rw [Set.indicator_of_notMem hb]
    exact le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hle)
      (integral_nonneg_of_ae hnn)
  dsimp [g] at hzero
  rw [integral_indicator hB, integral_const, smul_eq_mul,
    Measure.real, Measure.restrict_apply_univ] at hzero
  change P B = 0
  by_contra hne
  have hp : 0 < (P B).toReal := ENNReal.toReal_pos hne (measure_ne_top P B)
  exact (mul_pos hp (Real.exp_pos _)).ne' hzero
