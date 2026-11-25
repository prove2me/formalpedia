-- Prove2me | solution 1 for NashWilliams.toDigraph_toSimpleGraphInclusive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:31:48.190803+00:00
-- url     : https://prove2.me/submissions/13edf23c-e9fe-4069-9567-db0eda343ea5

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Orientation
public import Definitions.Def_NashWilliamsLib_Defs
public import Theorems.Thm_NashWilliams_adj_edgeEnds
public import Theorems.Thm_NashWilliams_edgeEnds_eq_or
public import Theorems.Thm_NashWilliams_toDigraph_adj_ends

set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V : Type*} (G : SimpleGraph V)
namespace NashWilliams
theorem _root_.solution (o : G.edgeSet → Bool) :
    (toDigraph G o).toSimpleGraphInclusive = G := by
  ext a b
  simp only [Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · obtain ⟨e, he | he⟩ := toDigraph_adj_ends G h
      · simpa [he] using adj_edgeEnds G e
      · simpa [he] using (adj_edgeEnds G e).symm
    · obtain ⟨e, he | he⟩ := toDigraph_adj_ends G h
      · simpa [he] using (adj_edgeEnds G e).symm
      · simpa [he] using adj_edgeEnds G e
  · intro h
    refine ⟨G.ne_of_adj h, ?_⟩
    set e : G.edgeSet := ⟨s(a, b), h⟩
    rcases edgeEnds_eq_or G (e := e) rfl with he | he <;> cases ho : o e
    · exact Or.inr ⟨e, by simp [ho, he]⟩
    · exact Or.inl ⟨e, by simp [ho, he]⟩
    · exact Or.inl ⟨e, by simp [ho, he]⟩
    · exact Or.inr ⟨e, by simp [ho, he]⟩
end NashWilliams
