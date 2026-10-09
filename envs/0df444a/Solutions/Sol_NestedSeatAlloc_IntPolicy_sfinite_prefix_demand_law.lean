-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.sfinite_prefix_demand_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T15:06:26.833746+00:00
-- url     : https://prove2.me/submissions/9015fa7d-d1f1-4763-b73e-b9be1c0a7b42

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_measurable_prefix_vector

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (hM : IsSeatModel P X f) (k : ℕ) :
    SFinite (Measure.map
      (fun ω : Ω => fun i : (Finset.Icc 1 k) => X i.1 ω) P) := by
  letI : IsProbabilityMeasure P := hM.isProb
  letI : IsProbabilityMeasure (Measure.map
      (fun ω : Ω => fun i : (Finset.Icc 1 k) => X i.1 ω) P) :=
    Measure.isProbabilityMeasure_map
      (measurable_prefix_vector P X f hM k).aemeasurable
  infer_instance
