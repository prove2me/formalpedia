-- Prove2me | solution 1 for Kyprianou.Ch02.jointLevyPairIndependentFiniteCylindersV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:26:13.215432+00:00
-- url     : https://prove2.me/submissions/e5afc73e-a778-4065-93f6-51f0743d695d

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_jointLevyPairIndependentGridValuesV1
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
    (I J : Finset ℝ≥0) :
    IndepFun (fun ω (i : I) => A i ω) (fun ω (j : J) => B j ω) P := by
  let K := I ∪ J
  let e := K.orderIsoOfFin rfl
  let t : Fin (K.card+1) → ℝ≥0 := Fin.cons 0 (fun i => (e i : ℝ≥0))
  have ht : Monotone t := by
    intro i j
    refine Fin.cases ?_ (fun i' => ?_) i
    · intro _
      exact zero_le
    · refine Fin.cases ?_ (fun j' => ?_) j
      · intro h
        have : i'.val + 1 ≤ 0 := h
        omega
      · intro h
        exact e.monotone (Fin.succ_le_succ_iff.mp h)
  have h := Kyprianou.Ch02.jointLevyPairIndependentGridValuesV1
    P A B hA0 hB0 hmA hmB hi hs hc K.card t ht rfl
  let f (i : I) : Fin (K.card+1) := (e.symm ⟨i.val,Finset.mem_union_left J i.property⟩).succ
  let g (j : J) : Fin (K.card+1) := (e.symm ⟨j.val,Finset.mem_union_right I j.property⟩).succ
  have hf : Measurable (fun v : Fin (K.card+1) → ℝ => fun i : I => v (f i)) := by fun_prop
  have hg : Measurable (fun v : Fin (K.card+1) → ℝ => fun j : J => v (g j)) := by fun_prop
  have h1 : (fun v : Fin (K.card+1) → ℝ => fun i : I => v (f i)) ∘
      (fun ω i => A (t i) ω) = (fun ω (i : I) => A i ω) := by
    funext ω i
    change A ((e (e.symm ⟨i.val,Finset.mem_union_left J i.property⟩) : K) : ℝ≥0) ω = _
    rw [e.apply_symm_apply]
  have h2 : (fun v : Fin (K.card+1) → ℝ => fun j : J => v (g j)) ∘
      (fun ω i => B (t i) ω) = (fun ω (j : J) => B j ω) := by
    funext ω j
    change B ((e (e.symm ⟨j.val,Finset.mem_union_right I j.property⟩) : K) : ℝ≥0) ω = _
    rw [e.apply_symm_apply]
  simpa only [h1,h2] using h.comp hf hg
