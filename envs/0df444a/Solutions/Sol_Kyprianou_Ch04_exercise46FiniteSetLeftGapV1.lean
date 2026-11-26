-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46FiniteSetLeftGapV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:21:34.611286+00:00
-- url     : https://prove2.me/submissions/c124551a-7470-42cf-9f25-ff7ab6cb9201

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    (S : Set NNReal) (hS : S.Finite) (t : NNReal) (ht : 0 < t) :
    ∃ s : NNReal, s < t ∧ ∀ u ∈ S, s < u → u < t → False := by
  classical
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    exact ⟨0,ht,by simp⟩
  | @insert a S ha hS ih =>
    obtain ⟨s,hs,hgap⟩ := ih
    by_cases hat : a < t
    · refine ⟨max a s,max_lt hat hs,?_⟩
      intro u hu hlu hut
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · exact (not_lt_of_ge (le_max_left u s)) hlu
      · exact hgap u hu ((le_max_right a s).trans_lt hlu) hut
    · refine ⟨s,hs,?_⟩
      intro u hu hlu hut
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · exact hat hut
      · exact hgap u hu hlu hut
