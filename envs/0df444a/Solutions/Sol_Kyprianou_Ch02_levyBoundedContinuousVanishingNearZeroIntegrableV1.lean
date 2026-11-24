-- Prove2me | solution 1 for Kyprianou.Ch02.levyBoundedContinuousVanishingNearZeroIntegrableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:01:19.958784+00:00
-- url     : https://prove2.me/submissions/3ec843c7-f2eb-4438-ba15-fa172957c105

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false
open Filter Topology Set

theorem solution
    (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    (f : BoundedContinuousFunction ℝ ℝ) (r : ℝ) (hr : 0 < r)
    (hf : ∀ x : ℝ, |x| < r → f x = 0) :
    Integrable (fun x : ℝ => f x) ν := by
  let s : Set ℝ := {x | r ≤ |x|}
  let c := ENNReal.ofReal (min 1 (r ^ 2))
  let g := fun x : ℝ => ENNReal.ofReal (min 1 (x ^ 2))
  have hc : 0 < c := ENNReal.ofReal_pos.mpr (lt_min one_pos (sq_pos_of_pos hr))
  have hg : Measurable g := by fun_prop
  have hsub : s ⊆ {x : ℝ | c ≤ g x} := by
    intro x hx
    apply ENNReal.ofReal_le_ofReal
    exact min_le_min le_rfl ((sq_abs x).symm ▸ pow_le_pow_left₀ hr.le hx 2)
  have hle : c * ν s ≤ ∫⁻ x, g x ∂ν :=
    (mul_le_mul_right (measure_mono hsub) c).trans (mul_meas_ge_le_lintegral hg c)
  have hfin : ν s < ⊤ :=
    ENNReal.lt_top_of_mul_ne_top_right (ne_top_of_le_ne_top hν.2.ne hle) hc.ne'
  letI : IsFiniteMeasure (ν.restrict s) := isFiniteMeasure_restrict.mpr hfin.ne
  have hs : MeasurableSet s := measurableSet_le measurable_const continuous_abs.measurable
  have hfs : IntegrableOn (fun x => f x) s ν :=
    BoundedContinuousFunction.integrable (μ := ν.restrict s) f
  refine ((integrable_indicator_iff hs).2 hfs).congr ?_
  filter_upwards [] with x
  by_cases hx : x ∈ s
  · simp [hx]
  · rw [Set.indicator_of_notMem hx]
    exact (hf x (lt_of_not_ge (show ¬ r ≤ |x| from hx))).symm
