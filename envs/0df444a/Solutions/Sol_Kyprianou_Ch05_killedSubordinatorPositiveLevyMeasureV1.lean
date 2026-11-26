-- Prove2me | solution 1 for Kyprianou.Ch05.killedSubordinatorPositiveLevyMeasureV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:51:31.075394+00:00
-- url     : https://prove2.me/submissions/93941313-1355-4079-8a96-00c26c2833c8

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05
theorem solution
    (eta d : ℝ) (Pi : Measure ℝ) (Phi : ℝ → ℝ)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi) :
    ProbabilityTheory.IsLevyMeasure Pi := by
  refine ⟨measure_mono_null (by intro x hx; simp only [mem_singleton_iff] at hx; simp [hx]) hTriplet.2.2.1,?_⟩
  have hres : Pi.restrict (Ioi (0 : ℝ)) = Pi := by
    apply Measure.restrict_eq_self_of_ae_mem
    apply ae_iff.mpr
    have hs : {x : ℝ | ¬ x ∈ Ioi (0 : ℝ)} = Iic 0 := by ext x; simp
    rw [hs]
    exact hTriplet.2.2.1
  rw [← hres]
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) hTriplet.2.2.2.1
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  apply ENNReal.ofReal_le_ofReal
  by_cases h : x ≤ 1
  · rw [min_eq_right h]
    exact (min_le_right _ _).trans (by nlinarith [show 0 < x from hx])
  · rw [min_eq_left (le_of_not_ge h)]
    exact min_le_left _ _
