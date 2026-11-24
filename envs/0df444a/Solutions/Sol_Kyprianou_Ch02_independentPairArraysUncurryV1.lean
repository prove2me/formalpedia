-- Prove2me | solution 1 for Kyprianou.Ch02.independentPairArraysUncurryV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:03:20.915611+00:00
-- url     : https://prove2.me/submissions/e96b6a1d-5446-4fb4-8a6a-0dcf7377ed09

import Theorems.Thm_Kyprianou_Ch02_indepFunToFinTwoV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (G : Fin n → Ω → ℝ × ℝ)
    (hm : ∀ i, Measurable (G i)) (hi : iIndepFun G P)
    (hc : ∀ i, IndepFun (fun ω => (G i ω).1) (fun ω => (G i ω).2) P) :
    iIndepFun (fun (p : Fin n × Fin 2) ω =>
      if p.2=0 then (G p.1 ω).1 else (G p.1 ω).2) P := by
  let g (p : ℝ × ℝ) (j : Fin 2) := if j=0 then p.1 else p.2
  have hg (j : Fin 2) : Measurable (fun p => g p j) := by
    by_cases hj : j=0 <;> simp [g,hj,measurable_fst,measurable_snd]
  let D (i : Fin n) (j : Fin 2) ω := g (G i ω) j
  apply iIndepFun_uncurry' (X:=D)
  · exact fun i j => (hg j).comp (hm i)
  · exact hi.comp (fun _ p => g p) (fun _ => measurable_pi_lambda _ hg)
  · intro i
    exact Kyprianou.Ch02.indepFunToFinTwoV1 P _ _ (hc i)
