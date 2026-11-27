-- Prove2me | solution 1 for MatchingPolytope.isMatching_matchingSubgraphOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:32:45.336323+00:00
-- url     : https://prove2.me/submissions/3b1e02b9-058b-4d8a-865c-62804e9ee6a0

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
public import Theorems.Thm_MatchingPolytope_Multi_mem_gcut_singleton_of_nodiag


set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {V : Type*} (G : SimpleGraph V)
namespace MatchingPolytope
theorem _root_.solution {M : Finset G.edgeSet}
    (hM : ∀ v, (gcut (edgeEnds G) M {v}).card ≤ 1) : (matchingSubgraphOf G M).IsMatching := by
  rintro v ⟨w, e, he, hew⟩
  refine ⟨w, ⟨e, he, hew⟩, fun w' hw' => ?_⟩
  obtain ⟨e', he', hew'⟩ := hw'
  have h1 : e ∈ gcut (edgeEnds G) M {v} := by
    rw [mem_gcut_singleton_of_nodiag fun e _ => G.not_isDiag_of_mem_edgeSet e.2]
    exact ⟨he, by simp [edgeEnds, hew]⟩
  have h2 : e' ∈ gcut (edgeEnds G) M {v} := by
    rw [mem_gcut_singleton_of_nodiag fun e _ => G.not_isDiag_of_mem_edgeSet e.2]
    exact ⟨he', by simp [edgeEnds, hew']⟩
  have := Finset.card_le_one.1 (hM v) e h1 e' h2
  subst this
  rw [hew] at hew'
  exact (Sym2.congr_right.1 hew').symm
end MatchingPolytope
