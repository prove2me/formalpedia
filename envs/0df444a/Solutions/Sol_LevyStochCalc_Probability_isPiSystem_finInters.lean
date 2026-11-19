-- Prove2me | solution 1 for LevyStochCalc.Probability.isPiSystem_finInters
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T02:52:30.112769+00:00
-- url     : https://prove2.me/submissions/58737457-61cb-49cc-8e07-ea59d2593d70

import Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F001

open MeasureTheory Filter Set
open LevyStochCalc.Probability

theorem solution {α : Type*} (s : ℕ → Set α) : IsPiSystem (finInters s) := by
  rintro A ⟨t₁, rfl⟩ B ⟨t₂, rfl⟩ _
  refine ⟨t₁ ∪ t₂, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iInter, Finset.mem_union]
  aesop
