-- Prove2me | solution 1 for Kyprianou.Ch02.indepFunToFinTwoV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:00:27.868956+00:00
-- url     : https://prove2.me/submissions/79167a61-8f10-4658-b6cc-dc268b5d0277

import Mathlib.Probability.Independence.Basic
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω β : Type} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P] (A B : Ω → β)
    (h : IndepFun A B P) :
    iIndepFun (fun (i : Fin 2) ω => if i=0 then A ω else B ω) P := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  have hc : ∀ T : Finset (Fin 2), T = ∅ ∨ T = {0} ∨ T = {1} ∨ T = {0,1} := by decide
  have hcases := hc S
  rcases hcases with rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simpa using h.measure_inter_preimage_eq_mul (sets 0) (sets 1)
      (hsets 0 (by simp)) (hsets 1 (by simp))
