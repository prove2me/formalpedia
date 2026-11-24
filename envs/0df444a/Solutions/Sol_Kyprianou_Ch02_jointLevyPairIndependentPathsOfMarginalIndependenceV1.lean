-- Prove2me | solution 1 for Kyprianou.Ch02.jointLevyPairIndependentPathsOfMarginalIndependenceV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:22:54.342507+00:00
-- url     : https://prove2.me/submissions/692807a5-8f6c-4e9c-8aac-c18a7cc5c74e

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_jointLevyPairIndependentFiniteCylindersV1
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
    (hc : ∀ t, IndepFun (A t) (B t) P)
    : IndepFun (fun ω t => A t ω) (fun ω t => B t ω) P := by
  exact IndepFun.process_indepFun_process₀ hmA hmB
    (Kyprianou.Ch02.jointLevyPairIndependentFiniteCylindersV1 P A B hA0 hB0 hmA hmB hi hs hc)
