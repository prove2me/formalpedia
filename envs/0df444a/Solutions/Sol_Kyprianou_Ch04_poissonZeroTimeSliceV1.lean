-- Prove2me | solution 1 for Kyprianou.Ch04.poissonZeroTimeSliceV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:27:30.730857+00:00
-- url     : https://prove2.me/submissions/648e2206-c27e-407e-b828-784f796ac93f

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_poissonCountZeroOfReferenceZero
open MeasureTheory Set LevyStochCalc.Poisson
open scoped ENNReal
set_option autoImplicit false

/-- A physical Poisson random measure has no mass at time zero, almost surely. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν) :
    referenceIntensity ν (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0 ∧
      ∀ᵐ ω ∂P, N.N ω (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0 := by
  have hz : referenceIntensity ν (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0 := by
    rw [referenceIntensity,Measure.prod_prod,
      Measure.restrict_apply (measurableSet_singleton _)]
    simp
  exact ⟨hz,Kyprianou.Ch04.poissonCountZeroOfReferenceZero P ν N _
    ((measurableSet_singleton _).prod MeasurableSet.univ) hz⟩
