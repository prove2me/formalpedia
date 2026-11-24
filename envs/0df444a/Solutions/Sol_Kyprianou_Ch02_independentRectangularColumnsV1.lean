-- Prove2me | solution 1 for Kyprianou.Ch02.independentRectangularColumnsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:03:28.538125+00:00
-- url     : https://prove2.me/submissions/89633b29-4766-435e-a9b6-ac9bce87152f

import Theorems.Thm_levy_foundations_iIndepFun_setRestrict_pairwiseDisjoint
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (D : Fin n × Fin 2 → Ω → ℝ)
    (hm : ∀ p, Measurable (D p)) (hi : iIndepFun D P) :
    IndepFun (fun ω (i : Fin n) => D (i,0) ω)
      (fun ω (i : Fin n) => D (i,1) ω) P := by
  let S (j : Fin 2) : Set (Fin n × Fin 2) := {p | p.2=j}
  have hS : Pairwise (Function.onFun Disjoint S) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro p hp hq
    exact hij (hp.symm.trans hq)
  have hb := levy_foundations_iIndepFun_setRestrict_pairwiseDisjoint hm hi hS
  let r (j : Fin 2) (z : S j → ℝ) (i : Fin n) := z ⟨(i,j),rfl⟩
  have hr (j : Fin 2) : Measurable (r j) := by fun_prop
  exact (hb.comp r hr).indepFun (i:=0) (j:=1) (by decide)
