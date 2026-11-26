-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_ucp_countable_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:14:51.827804+00:00
-- url     : https://prove2.me/submissions/fdd04da0-5fd7-4749-a2ea-35ff8cff472e

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Almost-sure convergence of a measurable error envelope implies UCP convergence,
even when the error event itself is not known to be measurable. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (E : ℕ → NNReal → Ω → ℝ) (B : ℕ → Ω → ℝ) (T : NNReal)
    (hB : ∀ n, AEStronglyMeasurable (B n) P)
    (hlim : ∀ᵐ w ∂P, Tendsto (fun n => B n w) atTop (nhds 0))
    (hbound : ∀ᵐ w ∂P, ∀ n t, t ≤ T → |E n t w| ≤ |B n w|)
    (e : ℝ) (he : 0 < e) :
    Tendsto (fun n => (P {w | ∃ t ≤ T, e ≤ |E n t w|}).toReal) atTop (nhds 0) := by
  have h := (tendstoInMeasure_iff_measureReal_norm.mp
    (tendstoInMeasure_of_tendsto_ae hB hlim)) e he
  simp only [measureReal_def, Pi.zero_apply, sub_zero, Real.norm_eq_abs] at h
  apply squeeze_zero (fun n => ENNReal.toReal_nonneg) _ h
  intro n
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hbound] with w hw
  rintro ⟨t,ht,he'⟩
  exact he'.trans (hw n t ht)
