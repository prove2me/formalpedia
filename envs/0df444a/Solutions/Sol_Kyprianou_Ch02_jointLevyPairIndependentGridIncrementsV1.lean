-- Prove2me | solution 1 for Kyprianou.Ch02.jointLevyPairIndependentGridIncrementsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:01:22.914668+00:00
-- url     : https://prove2.me/submissions/cadf2887-2834-439f-b18e-992e9668a854

import Theorems.Thm_Kyprianou_Ch02_independentPairArraysSeparateVectorsV1
import Theorems.Thm_Kyprianou_Ch02_indepFunOfPairIdentDistribV1
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
    (hc : ∀ t, IndepFun (A t) (B t) P)
    (n : ℕ) (t : Fin (n+1) → ℝ≥0) (ht : Monotone t) :
    IndepFun (fun ω (i : Fin n) => A (t i.succ) ω-A (t i.castSucc) ω)
      (fun ω (i : Fin n) => B (t i.succ) ω-B (t i.castSucc) ω) P := by
  let Y (t : ℝ≥0) (ω : Ω) := (A t ω,B t ω)
  let D (i : Fin n) := increment Y (t i.castSucc) (t i.succ)
  have hm (i : Fin n) : AEMeasurable (D i) P :=
    ((hmA _).prodMk (hmB _)).sub ((hmA _).prodMk (hmB _))
  have hD (i : Fin n) : IndepFun (fun ω => (D i ω).1) (fun ω => (D i ω).2) P := by
    have h := hs (t i.castSucc) (t i.succ-t i.castSucc)
    rw [add_tsub_cancel_of_le (ht (Fin.castSucc_le_succ i))] at h
    have he : increment Y 0 (t i.succ-t i.castSucc) = Y (t i.succ-t i.castSucc) := by
      funext ω
      simp [increment,Y,hA0,hB0]
    change IdentDistrib (D i) (increment Y 0 _) P P at h
    rw [he] at h
    exact Kyprianou.Ch02.indepFunOfPairIdentDistribV1 P _ _ h (hc _)
  exact Kyprianou.Ch02.independentPairArraysSeparateVectorsV1 P n D hm (hi n t ht) hD
