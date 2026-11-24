-- Prove2me | solution 1 for Kyprianou.Ch02.jointLevyPairIndependentFiniteRestrictionsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:26:48.778533+00:00
-- url     : https://prove2.me/submissions/01579641-b471-4660-ac74-38dbda5583ec

import Theorems.Thm_Kyprianou_Ch02_jointLevyPairIndependentFiniteCylindersV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : ℝ≥0 → Ω → ℝ)
    (hA0 : A 0 = fun _ => 0) (hB0 : B 0 = fun _ => 0)
    (hmA : ∀ t, AEMeasurable (A t) P) (hmB : ∀ t, AEMeasurable (B t) P)
    (hi : HasIndependentIncrements (fun t ω => (A t ω,B t ω)) P)
    (hs : HasStationaryIncrements (fun t ω => (A t ω,B t ω)) P)
    (hc : ∀ t, IndepFun (A t) (B t) P) :
    ∀ I J : Finset ℝ≥0,
      IndepFun (fun ω (i : I) => A i ω) (fun ω (j : J) => B j ω) P := by
  exact Kyprianou.Ch02.jointLevyPairIndependentFiniteCylindersV1 P A B hA0 hB0 hmA hmB hi hs hc
