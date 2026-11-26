-- Prove2me | solution 1 for Kyprianou.Ch04.negativeCompensationLedgerV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:00:48.858169+00:00
-- url     : https://prove2.me/submissions/f6ccffee-94f1-42f9-a20b-ef2c59b23afd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_ProbabilityTheory_integrable_levyCompensatedIntegrand
import Theorems.Thm_AvramDividend_Classical_boundedVariation_min_one_abs_integrable
open MeasureTheory ProbabilityTheory Set Complex AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Integrable compensation and pointwise uncompensated negative-jump kernel. -/
theorem solution (ν : Measure ℝ)
    (hn : ∀ᵐ y ∂ν, y < 0)
    (hint : Integrable (fun y : ℝ => min 1 |y|) ν)
    (ξ : ℝ) :
    let l : ℝ → ℝ := (Ioo (-1 : ℝ) 0).indicator id
    Integrable (fun y => (l y : ℂ) * (ξ : ℂ) * I) ν ∧
      (fun y : ℝ => Complex.exp (I * ((ξ * y : ℝ) : ℂ)) - 1) =ᵐ[ν]
        (fun y => levyCompensatedIntegrand ξ y + (l y : ℂ) * (ξ : ℂ) * I) := by
  let l : ℝ → ℝ := (Ioo (-1 : ℝ) 0).indicator id
  have hl : Integrable l ν := by
    apply hint.mono'
    · exact (measurable_id.indicator measurableSet_Ioo).aestronglyMeasurable
    · filter_upwards with y
      by_cases hy : y ∈ Ioo (-1 : ℝ) 0
      · have h : |y| ≤ 1 := by rw [abs_of_neg hy.2]; linarith [hy.1]
        simp [l, Set.indicator_of_mem hy, Real.norm_eq_abs, min_eq_right h]
      · simp [l, Set.indicator_of_notMem hy]
  have hlc : Integrable (fun y => (l y : ℂ) * (ξ : ℂ) * I) ν :=
    (hl.ofReal.mul_const (ξ : ℂ)).mul_const I
  have heq : (fun y : ℝ => Complex.exp (I * ((ξ * y : ℝ) : ℂ)) - 1) =ᵐ[ν]
      (fun y => levyCompensatedIntegrand ξ y + (l y : ℂ) * (ξ : ℂ) * I) := by
    filter_upwards [hn] with y hy
    have he : I * ((ξ * y : ℝ) : ℂ) = (y : ℂ) * (ξ : ℂ) * I := by push_cast; ring
    rw [he]
    by_cases h : -1 < y
    · have hm : y ∈ Ioo (-1 : ℝ) 0 := ⟨h, hy⟩
      have ha : |y| < 1 := by rw [abs_of_neg hy]; linarith
      simp [levyCompensatedIntegrand, l, Set.indicator_of_mem hm, ha]
    · have hm : y ∉ Ioo (-1 : ℝ) 0 := fun hh => h hh.1
      have ha : ¬ |y| < 1 := by rw [abs_of_neg hy]; linarith
      simp [levyCompensatedIntegrand, l, Set.indicator_of_notMem hm, ha]
  exact ⟨hlc, heq⟩
