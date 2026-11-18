-- Prove2me | solution 1 for Kyprianou.ProofPreparation.measure_large_values_lt_top_of_integrable_truncated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T13:25:35.416185+00:00
-- url     : https://prove2.me/submissions/4e540f08-2208-4aee-a582-263e495081de

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

/-- Truncated integrability forces the large-value intensity to be finite. -/
theorem solution
    {E : Type} [MeasurableSpace E] (m : Measure E)
    (f : E → ℝ) (hf : Measurable f)
    (htrunc : Integrable (fun x => min (1 : ℝ) |f x|) m) :
    m {x | 1 < |f x|} < ⊤ := by
  let S : Set E := {x | 1 < |f x|}
  have hS : MeasurableSet S := measurableSet_lt measurable_const hf.abs
  have hInt : Integrable (S.indicator (fun _ => (1 : ℝ))) m := by
    apply htrunc.mono (measurable_const.indicator hS).aestronglyMeasurable
    filter_upwards with x
    by_cases hx : x ∈ S
    · have hx' : 1 ≤ |f x| := le_of_lt hx
      simpa [Set.indicator_of_mem hx, min_eq_left hx', Real.norm_eq_abs]
        using (le_refl (1 : ℝ))
    · have hn : (0 : ℝ) ≤ min 1 |f x| :=
        le_min (by norm_num) (abs_nonneg (f x))
      simpa [Set.indicator_of_notMem hx] using hn
  have hOn : IntegrableOn (fun _ : E => (1 : ℝ)) S m :=
    (integrable_indicator_iff hS).mp hInt
  rcases (integrableOn_const_iff (C := (1 : ℝ))).mp hOn with hz | hm
  · norm_num at hz
  · exact hm
