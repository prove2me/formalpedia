-- Prove2me | solution 1 for Kyprianou.Ch02.independentRealPathsOfFiniteRestrictionsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:26:39.907802+00:00
-- url     : https://prove2.me/submissions/4c2063ac-8e0d-4c8c-ba1c-91ddad942e6e

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : ℝ≥0 → Ω → ℝ)
    (hmA : ∀ t, AEMeasurable (A t) P) (hmB : ∀ t, AEMeasurable (B t) P)
    (h : ∀ I J : Finset ℝ≥0,
      IndepFun (fun ω (i : I) => A i ω) (fun ω (j : J) => B j ω) P) :
    IndepFun (fun ω t => A t ω) (fun ω t => B t ω) P := by
  exact IndepFun.process_indepFun_process₀ hmA hmB h
