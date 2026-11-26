-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45EventuallyAbsentEventsV5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:23:16.573056+00:00
-- url     : https://prove2.me/submissions/f1dee9d6-55a2-4f58-8db0-8aa3a5fa7f6f

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Measurable events which eventually disappear almost surely have vanishing probability. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A E : ℕ → Set Ω) (hm : ∀ n, MeasurableSet (A n))
    (hlim : ∀ᵐ w ∂P, ∀ᶠ n in atTop, w ∉ A n)
    (hb : ∀ n, ∀ᵐ w ∂P, w ∈ E n → w ∈ A n) :
    Tendsto (fun n => (P (E n)).toReal) atTop (nhds 0) := by
  let B (n : ℕ) : Ω → ℝ := (A n).indicator (fun _ => 1)
  have hB (n : ℕ) : AEStronglyMeasurable (B n) P :=
    (measurable_const.indicator (hm n)).aestronglyMeasurable
  have hconv : ∀ᵐ w ∂P, Tendsto (fun n => B n w) atTop (nhds 0) := by
    filter_upwards [hlim] with w hw
    apply tendsto_const_nhds.congr'
    filter_upwards [hw] with n hn
    simp [B,hn]
  have h := (tendstoInMeasure_iff_measureReal_norm.mp
    (tendstoInMeasure_of_tendsto_ae hB hconv)) 1 (by norm_num)
  simp only [measureReal_def,Pi.zero_apply,sub_zero,Real.norm_eq_abs] at h
  apply squeeze_zero (fun n => ENNReal.toReal_nonneg) _ h
  intro n
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hb n] with w hw hmem
  change 1 ≤ |B n w|
  simp [B,hw hmem]
