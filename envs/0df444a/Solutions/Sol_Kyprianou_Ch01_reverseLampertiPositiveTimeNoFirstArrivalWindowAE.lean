-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiPositiveTimeNoFirstArrivalWindowAE
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:30:11.169877+00:00
-- url     : https://prove2.me/submissions/29538806-930c-4164-bb52-c99e002e2379

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiBeforeFirstArrivalOccupationWitness
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiConstantPrefixFromOccupationWitness
import Theorems.Thm_Kyprianou_Ch01_reverseIntegerCompoundPoissonConstantBeforeFirstArrival
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q) :
    ∀ (y : ℕ) (t : ℝ≥0), 0 < t → ∀ᵐ ω ∂Q,
      (y : ℝ) * (t : ℝ) < ProbabilityTheory.arrival arrival 0 ω →
      (compoundPoissonToBranching
      (integerCompoundPoisson y arrival marks) t ω).toNat = y := by
  intro y t ht
  filter_upwards [] with ω hBefore
  have hWitness :=
    Kyprianou.Ch01.reverseLampertiBeforeFirstArrivalOccupationWitness
      y arrival marks t ω hBefore
  apply Kyprianou.Ch01.reverseLampertiConstantPrefixFromOccupationWitness
    (integerCompoundPoisson y arrival marks) ω y t
    (ProbabilityTheory.arrival arrival 0 ω)
  · intro u hu
    exact Kyprianou.Ch01.reverseIntegerCompoundPoissonConstantBeforeFirstArrival
      y arrival marks u ω hu
  · exact hWitness
