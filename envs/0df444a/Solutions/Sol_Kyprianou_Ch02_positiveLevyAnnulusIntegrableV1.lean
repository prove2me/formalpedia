-- Prove2me | solution 1 for Kyprianou.Ch02.positiveLevyAnnulusIntegrableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:10:26.83445+00:00
-- url     : https://prove2.me/submissions/37fa1831-3b1d-4d68-aa3a-d65491c92afb

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => x) (Set.Ico r 1) ν := by
  have hsub : Set.Ico r 1 ⊆ {x : ℝ | r ≤ |x|} :=
    fun x hx => hx.1.trans (le_abs_self x)
  have hfin : ν (Set.Ico r 1) < ⊤ :=
    (measure_mono hsub).trans_lt (hν.measure_setOf_abs_ge_lt_top hr)
  letI : IsFiniteMeasure (ν.restrict (Set.Ico r 1)) :=
    isFiniteMeasure_restrict.mpr hfin.ne
  refine (integrable_const (1 : ℝ) (μ := ν.restrict (Set.Ico r 1))).mono'
    continuous_id.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (μ := ν) measurableSet_Ico] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (hr.le.trans hx.1)]
  exact hx.2.le
