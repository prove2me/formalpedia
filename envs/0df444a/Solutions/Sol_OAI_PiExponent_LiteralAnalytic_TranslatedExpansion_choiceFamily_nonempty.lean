-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.choiceFamily_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:21:00.386842+00:00
-- url     : https://prove2.me/submissions/88831a86-1908-4deb-9a33-e15bbbb9c3b7

import Mathlib
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion
theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    Nonempty (ChoiceFamily d H) := by
  have h0 : (Finsupp.equivFunOnFinite.symm (0 : Fin d.m → ℕ)) ∈ indices d H := by
    simp only [indices, Finset.mem_map, Equiv.coe_toEmbedding]
    refine ⟨0, ?_, rfl⟩
    simp only [realWeightedSimplex, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨fun i => by simp, ?_⟩
    simp [hH.le]
  exact ⟨fun r => ⟨⟨_, h0⟩, fun i => 0, 0⟩⟩
