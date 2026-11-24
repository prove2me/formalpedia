-- Prove2me | solution 2 for Kyprianou.Ch02.jointLevyPairIndependentPathsOfMarginalIndependenceV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:23:39.366778+00:00
-- url     : https://prove2.me/submissions/78f08996-50ef-4b19-9725-6e459a065ffd

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_jointLevyPairIndependentFiniteRestrictionsV1
import Theorems.Thm_Kyprianou_Ch02_independentRealPathsOfFiniteRestrictionsV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Extend finite-dimensional independence to the full paths. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : ℝ≥0 → Ω → ℝ)
    (hA0 : A 0 = fun _ => 0) (hB0 : B 0 = fun _ => 0)
    (hmA : ∀ t, AEMeasurable (A t) P) (hmB : ∀ t, AEMeasurable (B t) P)
    (hi : HasIndependentIncrements (fun t ω => (A t ω,B t ω)) P)
    (hs : HasStationaryIncrements (fun t ω => (A t ω,B t ω)) P)
    (hc : ∀ t, IndepFun (A t) (B t) P) :
    IndepFun (fun ω t => A t ω) (fun ω t => B t ω) P := by
  exact Kyprianou.Ch02.independentRealPathsOfFiniteRestrictionsV1
    P A B hmA hmB
    (Kyprianou.Ch02.jointLevyPairIndependentFiniteRestrictionsV1
      P A B hA0 hB0 hmA hmB hi hs hc)
