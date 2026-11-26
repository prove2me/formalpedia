-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41VisitEndpointV19
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:01:34.675031+00:00
-- url     : https://prove2.me/submissions/4aa31288-fe37-49b2-b6e2-235974dfc26f

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    (x : NNReal → ℝ) (t : NNReal)
    (ht : 0 < t)
    (hv : Set.Finite {s : NNReal | 0 < s ∧ s ≤ t ∧ x s = 0}) :
    (∑ s ∈ hv.toFinset, (if x s = 0 then (1 : ℝ) else 0)) =
      (∑ s ∈ hv.toFinset, (if s < t then (1 : ℝ) else 0)) +
      (if x t = 0 then 1 else 0) := by
  classical
  have hsplit : (∑ s ∈ hv.toFinset, (if x s = 0 then (1 : ℝ) else 0)) =
      ∑ s ∈ hv.toFinset, ((if s < t then (1 : ℝ) else 0) + (if s = t then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro s hs
    have h := hv.mem_toFinset.mp hs
    by_cases he : s = t
    · subst s
      simp [h.2.2]
    · simp [h.2.2,lt_of_le_of_ne h.2.1 he,he]
  rw [hsplit,Finset.sum_add_distrib,Finset.sum_ite_eq']
  have he : t ∈ hv.toFinset ↔ x t = 0 := by simp [ht]
  simp [he]
