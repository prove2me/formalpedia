-- Prove2me | solution 1 for Kyprianou.Ch02.positiveSmallTimeTestBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:11:05.924082+00:00
-- url     : https://prove2.me/submissions/98f3be05-2377-4289-b83e-85f9f50236cc

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (M : {t : ℝ // 0 < t} → ProbabilityMeasure ℝ)
    (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    (hM : ∀ t, (M t : Measure ℝ) (Set.Iio (0 : ℝ)) = 0)
    (r b : ℝ) (hr : 0 < r) (ts : ℕ → {t : ℝ // 0 < t})
    (hb : Tendsto (fun n => (ts n).val⁻¹ *
      ∫ x in {x : ℝ | |x| < r}, x ∂(M (ts n) : Measure ℝ)) atTop (nhds b))
    (hjump : ∀ f : BoundedContinuousFunction ℝ ℝ,
      (∃ δ > 0, ∀ x, |x| < δ → f x = 0) →
      Tendsto (fun n => (ts n).val⁻¹ * ∫ x, f x ∂(M (ts n) : Measure ℝ))
        atTop (nhds (∫ x, f x ∂ν)))
    (f : BoundedContinuousFunction ℝ ℝ)
    (hf : ∀ x, f x ≤ (Set.Ioo (0 : ℝ) r).indicator id x)
    (hzero : ∃ δ > 0, ∀ x, |x| < δ → f x = 0) :
    (∫ x, f x ∂ν) ≤ b := by
  apply le_of_tendsto_of_tendsto' (hjump f hzero) hb
  intro n
  let μ : Measure ℝ := M (ts n)
  let s : Set ℝ := {x | |x| < r}
  have hs : MeasurableSet s := (isOpen_lt continuous_abs continuous_const).measurableSet
  let g : ℝ → ℝ := s.indicator id
  have hg : Integrable g μ := by
    apply (integrable_const r).mono' (measurable_id.indicator hs).aestronglyMeasurable
    filter_upwards with x
    by_cases hx : x ∈ s
    · simpa [g, hx, Real.norm_eq_abs] using (show |x| ≤ r from le_of_lt hx)
    · simp [g, hx, hr.le]
  have hnonneg : ∀ᵐ x ∂μ, 0 ≤ x := by
    rw [ae_iff]
    simp only [not_le]
    exact hM (ts n)
  have hle : ∀ᵐ x ∂μ, f x ≤ g x := by
    filter_upwards [hnonneg] with x hx
    apply (hf x).trans
    by_cases hx0 : x = 0
    · subst x
      simp [g, s, hr]
    · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      by_cases hxr : x < r
      · have hsx : x ∈ s := by simpa [s, abs_of_nonneg hx] using hxr
        have hix : x ∈ Ioo (0 : ℝ) r := ⟨hxpos, hxr⟩
        simp only [g, indicator_of_mem hsx, indicator_of_mem hix]
        exact le_rfl
      · have hsx : x ∉ s := by simpa [s, abs_of_nonneg hx] using hxr
        have hix : x ∉ Ioo (0 : ℝ) r := fun h => hxr h.2
        simp only [g, indicator_of_notMem hsx, indicator_of_notMem hix]
        exact le_rfl
  apply mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (le_of_lt (ts n).property))
  rw [← integral_indicator hs]
  exact integral_mono_ae (f.integrable (μ := μ)) hg hle
