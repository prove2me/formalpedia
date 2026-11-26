-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52IntegratedTailFiniteMeanV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:23:10.576353+00:00
-- url     : https://prove2.me/submissions/0908943d-29d5-4a52-a0d7-b4eb933d00eb

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch05_RiskConditionalPassage
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set
open Kyprianou.Ch05
/-- The integrated-tail law has finite mean under the weighted-tail integrability condition. -/
theorem solution
    (nu : Measure ℝ) (m : ℝ) (hm : 0 < m)
    (hInt : IntegrableOn (fun z : ℝ => z * (nu (Ioi z)).toReal) (Ioi 0) volume) :
    Integrable (fun z : ℝ => z) (ascendingRecordJumpDistribution nu m) := by
  have hTail : Antitone (fun z : ℝ => nu (Ioi z)) :=
    fun _ _ h => measure_mono (Ioi_subset_Ioi h)
  let f : ℝ → ENNReal := fun z => ENNReal.ofReal ((nu (Ioi z)).toReal / m)
  have hf : Measurable f := ENNReal.measurable_ofReal.comp
    ((ENNReal.measurable_toReal.comp hTail.measurable).div_const m)
  change Integrable (fun z : ℝ => z) ((volume.restrict (Ioi 0)).withDensity f)
  apply (integrable_withDensity_iff hf (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).2
  have hEq : (fun z : ℝ => z * (f z).toReal) =
      (fun z : ℝ => (z * (nu (Ioi z)).toReal) / m) := by
    funext z
    change z * (ENNReal.ofReal ((nu (Ioi z)).toReal / m)).toReal =
      z * (nu (Ioi z)).toReal / m
    rw [ENNReal.toReal_ofReal (div_nonneg ENNReal.toReal_nonneg hm.le)]
    ring
  rw [hEq]
  exact hInt.div_const m
