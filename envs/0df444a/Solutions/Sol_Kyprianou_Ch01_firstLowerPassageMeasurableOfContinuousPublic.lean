-- Prove2me | solution 1 for Kyprianou.Ch01.firstLowerPassageMeasurableOfContinuousPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T09:06:12.975058+00:00
-- url     : https://prove2.me/submissions/00898a92-b0a9-4a42-8756-172943a83a22

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_firstLowerPassageEqShiftedNegUpperPublic
import Theorems.Thm_Kyprianou_Ch01_firstUpperPassageMeasurableOfContinuousPublic
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (x barrier : ℝ) :
    Measurable (firstLowerPassage X x barrier) := by
  have hnegMeas : ∀ t : ℝ≥0,
      Measurable (fun ω => -X t ω) :=
    fun t => (hMeas t).neg
  have hnegCont : ∀ ω,
      Continuous (fun t : ℝ≥0 => -X t ω) :=
    fun ω => (hContinuous ω).neg
  rw [Kyprianou.Ch01.firstLowerPassageEqShiftedNegUpperPublic
    X x barrier]
  exact Kyprianou.Ch01.firstUpperPassageMeasurableOfContinuousPublic
    (fun t ω => -X t ω) hnegMeas hnegCont (x - barrier)
