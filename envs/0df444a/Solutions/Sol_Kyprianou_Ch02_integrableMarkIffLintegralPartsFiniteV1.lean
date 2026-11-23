-- Prove2me | solution 1 for Kyprianou.Ch02.integrableMarkIffLintegralPartsFiniteV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:05:59.159983+00:00
-- url     : https://prove2.me/submissions/20757253-e121-4f0b-8785-be000bbda61f

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    (μ : Measure (ℝ × ℝ)) (R : Set (ℝ × ℝ)) (hR : MeasurableSet R) :
    Integrable (fun z : ℝ × ℝ => z.2) (μ.restrict R) ↔
      (∫⁻ z in R, ENNReal.ofReal z.2 ∂μ) ≠ ⊤ ∧
      (∫⁻ z in R, ENNReal.ofReal (-z.2) ∂μ) ≠ ⊤ := by
  have hpIff :
      (∫⁻ z in R, ENNReal.ofReal z.2 ∂μ) ≠ ⊤ ↔
        Integrable (fun z : ℝ × ℝ => max z.2 0) (μ.restrict R) := by
    have hm : AEStronglyMeasurable
        (fun z : ℝ × ℝ => max z.2 0) (μ.restrict R) :=
      (measurable_snd.max measurable_const).aestronglyMeasurable
    have hnonneg : ∀ᵐ z : ℝ × ℝ ∂(μ.restrict R), 0 ≤ max z.2 0 :=
      Filter.Eventually.of_forall fun z => le_max_right _ _
    simpa [ENNReal.ofReal_max] using
      (lintegral_ofReal_ne_top_iff_integrable hm hnonneg)
  have hnIff :
      (∫⁻ z in R, ENNReal.ofReal (-z.2) ∂μ) ≠ ⊤ ↔
        Integrable (fun z : ℝ × ℝ => max (-z.2) 0) (μ.restrict R) := by
    have hm : AEStronglyMeasurable
        (fun z : ℝ × ℝ => max (-z.2) 0) (μ.restrict R) :=
      (measurable_snd.neg.max measurable_const).aestronglyMeasurable
    have hnonneg : ∀ᵐ z : ℝ × ℝ ∂(μ.restrict R), 0 ≤ max (-z.2) 0 :=
      Filter.Eventually.of_forall fun z => le_max_right _ _
    simpa [ENNReal.ofReal_max] using
      (lintegral_ofReal_ne_top_iff_integrable hm hnonneg)
  constructor
  · intro hi
    exact ⟨hpIff.mpr hi.pos_part, hnIff.mpr hi.neg_part⟩
  · rintro ⟨ha, hb⟩
    have hf : (fun z : ℝ × ℝ => z.2) =
        (fun z : ℝ × ℝ => max z.2 0 - max (-z.2) 0) := by
      funext z
      exact (max_zero_sub_max_neg_zero_eq_self z.2).symm
    rw [hf]
    exact (hpIff.mp ha).sub (hnIff.mp hb)
