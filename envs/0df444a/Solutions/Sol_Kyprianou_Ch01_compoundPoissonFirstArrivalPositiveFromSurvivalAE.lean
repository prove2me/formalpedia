-- Prove2me | solution 1 for Kyprianou.Ch01.compoundPoissonFirstArrivalPositiveFromSurvivalAE
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:16:16.003485+00:00
-- url     : https://prove2.me/submissions/5d00282d-2da5-42da-9bef-c8aae0ceb975

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiFirstArrivalSurvival
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
 :
    ∀ᵐ ω ∂Q, 0 < ProbabilityTheory.arrival arrival 0 ω := by
  have hArrMeas : Measurable
      (ProbabilityTheory.arrival arrival 0) := by
    have hf : ProbabilityTheory.arrival arrival 0 = arrival 0 := by
      funext ω
      simp [ProbabilityTheory.arrival]
    rw [hf]
    exact hdriver.measurable_interarrival 0
  have hMeas : MeasurableSet
      {ω : Ω | 0 < ProbabilityTheory.arrival arrival 0 ω} := by
    simpa only [Set.preimage, Set.mem_setOf_eq, Set.Ioi] using
      (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ))).preimage hArrMeas
  have hSurv :=
    Kyprianou.Ch01.reverseLampertiFirstArrivalSurvival
      Q rate hrate arrival marks jumpLaw hdriver 0 0
  have hr :
      (Q {ω : Ω | 0 < ProbabilityTheory.arrival arrival 0 ω}).toReal = 1 := by
    simpa using hSurv
  have hq :
      Q {ω : Ω | 0 < ProbabilityTheory.arrival arrival 0 ω} = 1 :=
    (ENNReal.toReal_eq_one_iff _).mp hr
  apply (ae_iff).2
  have hComp := measure_compl hMeas (measure_ne_top Q _)
  simpa [Set.compl_setOf, hq] using hComp
