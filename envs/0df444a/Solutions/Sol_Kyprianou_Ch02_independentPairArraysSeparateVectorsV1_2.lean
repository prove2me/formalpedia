-- Prove2me | solution 2 for Kyprianou.Ch02.independentPairArraysSeparateVectorsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:29:31.198668+00:00
-- url     : https://prove2.me/submissions/41047bc4-81e4-4bcc-96f6-afba6cdeca44

import Theorems.Thm_Kyprianou_Ch02_independentPairFamilyProjectionsV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (F : Fin n → Ω → ℝ × ℝ)
    (hm : ∀ i, AEMeasurable (F i) P) (hi : iIndepFun F P)
    (hc : ∀ i, IndepFun (fun ω => (F i ω).1) (fun ω => (F i ω).2) P) :
    IndepFun (fun ω i => (F i ω).1) (fun ω i => (F i ω).2) P := by
  exact Kyprianou.Ch02.independentPairFamilyProjectionsV1 P n
    (fun i ω => (F i ω).1) (fun i ω => (F i ω).2)
    (fun i => (hm i).fst) (fun i => (hm i).snd) hi hc
