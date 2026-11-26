-- Prove2me | solution 1 for Kyprianou.Ch05.cutoffShiftTailIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:19:34.767123+00:00
-- url     : https://prove2.me/submissions/cdee6c01-669f-4561-8105-cc5492d6fec0

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess

open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Cutoff shifted nonnegative antitone tail inherits integrability. -/
theorem solution
    (g : Real → Real) (hg : Antitone g) (hn : ∀ t, 0 ≤ g t)
    (hi : IntegrableOn g (Ioi (0 : Real))) (u y : Real) (hu : 0 < u) (hy : 0 < y) :
    Integrable (fun t : Real => if y < t then g (t+u) else 0) := by
  have hI := (integrable_indicator_iff measurableSet_Ioi).mpr hi
  apply hI.mono (Measurable.ite measurableSet_Ioi
    (hg.measurable.comp (measurable_id.add_const u)) measurable_const).aestronglyMeasurable
  filter_upwards [] with t
  by_cases ht : y < t
  · have hp : 0 < t := hy.trans ht
    rw [if_pos ht, indicator_of_mem (mem_Ioi.mpr hp)]
    change ‖g (t+u)‖ ≤ ‖g t‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hn (t+u)), abs_of_nonneg (hn t)]
    exact hg (by linarith : t ≤ t+u)
  · simp [ht]
