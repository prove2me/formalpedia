-- Prove2me | solution 1 for MarkovChainCLT.abs_integral_sub_le_tvDist_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T22:01:52.469729+00:00
-- url     : https://prove2.me/submissions/aec68264-f6a1-4a93-9358-9f74a6db384b

import Theorems.Thm_MarkovChainCLT_abs_integral_sub_le_tvDist

open MeasureTheory
open MarkovChainCLT
open scoped ENNReal NNReal

set_option maxHeartbeats 1000000

/-- Total variation controls differences of integrals of any bounded function. -/
theorem solution {X : Type*} [MeasurableSpace X] (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (g : X → ℝ) (hg : Measurable g) (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ x, |g x| ≤ M) :
    |∫ x, g x ∂μ - ∫ x, g x ∂ν| ≤ 2 * M * tvDist μ ν := by
  rcases eq_or_lt_of_le hM0 with hM0' | hMpos
  · -- degenerate case `M = 0`: then `g = 0`
    have hgz : ∀ x, g x = 0 := by
      intro x
      have := hM x
      rw [← hM0'] at this
      exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
    simp [hgz, ← hM0']
  -- rescale `g` into `[0, 1]`
  set h : X → ℝ := fun x => (g x + M) / (2 * M) with hh
  have h2M : (0:ℝ) < 2 * M := by linarith
  have hhm : Measurable h := (hg.add_const M).div_const _
  have hh0 : ∀ x, 0 ≤ h x := by
    intro x
    have := (abs_le.mp (hM x)).1
    rw [hh]
    exact div_nonneg (by linarith) (by linarith)
  have hh1 : ∀ x, h x ≤ 1 := by
    intro x
    have := (abs_le.mp (hM x)).2
    rw [hh, div_le_one h2M]
    linarith
  have hgint : ∀ (ρ : Measure X), IsProbabilityMeasure ρ → Integrable g ρ := by
    intro ρ hρ
    haveI := hρ
    refine ⟨hg.aestronglyMeasurable, ?_⟩
    refine (hasFiniteIntegral_const M).mono ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hM0]
    exact hM x
  have hval : ∀ (ρ : Measure X), IsProbabilityMeasure ρ →
      ∫ x, h x ∂ρ = ((∫ x, g x ∂ρ) + M) / (2 * M) := by
    intro ρ hρ
    haveI := hρ
    rw [hh]
    rw [integral_div, integral_add (hgint ρ hρ) (integrable_const M), integral_const]
    simp [Measure.real]
  have hkey := MarkovChainCLT.abs_integral_sub_le_tvDist μ ν h hhm hh0 hh1
  rw [hval μ inferInstance, hval ν inferInstance, div_sub_div_same, abs_div,
    abs_of_pos h2M, div_le_iff₀ h2M] at hkey
  have hsimp : (∫ x, g x ∂μ) + M - ((∫ x, g x ∂ν) + M) = (∫ x, g x ∂μ) - ∫ x, g x ∂ν := by ring
  rw [hsimp] at hkey
  linarith [hkey]
