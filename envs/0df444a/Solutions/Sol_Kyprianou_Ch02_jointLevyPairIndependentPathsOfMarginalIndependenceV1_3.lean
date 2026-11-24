-- Prove2me | solution 3 for Kyprianou.Ch02.jointLevyPairIndependentPathsOfMarginalIndependenceV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:24:48.226596+00:00
-- url     : https://prove2.me/submissions/f3b82ea4-3b11-4984-89e4-6f56a9de5f13

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_jointLevyPairIndependentGridIncrementsV1
import Theorems.Thm_Kyprianou_Ch02_finiteTimeSetsCommonZeroGridV1
import Theorems.Thm_Kyprianou_Ch02_indepGridIncrementsToGridValuesV1
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
    IndepFun (fun ω t => A t ω) (fun ω t => B t ω) P := by
  classical
  apply IndepFun.process_indepFun_process₀ hmA hmB
  intro I J
  obtain ⟨n,t,ht,ht0,hI,hJ⟩ := Kyprianou.Ch02.finiteTimeSetsCommonZeroGridV1 I J
  choose i hi' using hI
  choose j hj' using hJ
  have h := Kyprianou.Ch02.jointLevyPairIndependentGridIncrementsV1 P A B
    hA0 hB0 hmA hmB hi hs hc n t ht
  have hv := Kyprianou.Ch02.indepGridIncrementsToGridValuesV1 P A B hA0 hB0 n t ht0 h
  have hf : Measurable (fun v : Fin (n+1) → ℝ => fun k : I => v (i k)) :=
    measurable_pi_lambda _ fun k => measurable_pi_apply _
  have hg : Measurable (fun v : Fin (n+1) → ℝ => fun k : J => v (j k)) :=
    measurable_pi_lambda _ fun k => measurable_pi_apply _
  simpa only [Function.comp_def, hi', hj'] using hv.comp hf hg
