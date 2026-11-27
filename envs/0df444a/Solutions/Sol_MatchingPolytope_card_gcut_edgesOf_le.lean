-- Prove2me | solution 1 for MatchingPolytope.card_gcut_edgesOf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:32:52.269081+00:00
-- url     : https://prove2.me/submissions/5b930306-7b49-4631-beb6-2335ef395b3e

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
public import Theorems.Thm_MatchingPolytope_Multi_Valid_pair_of_mem
public import Theorems.Thm_MatchingPolytope_Multi_mem_gcut_singleton
public import Theorems.Thm_MatchingPolytope_mem_edgesOf
public import Theorems.Thm_MatchingPolytope_valid_edgeSet


set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace MatchingPolytope
theorem _root_.solution {M : G.Subgraph} (hM : M.IsMatching) (v : V) :
    (gcut (edgeEnds G) (edgesOf G M) {v}).card ≤ 1 := by
  apply Finset.card_le_one.2
  intro e he e' he'
  rw [mem_gcut_singleton (valid_edgeSet G) (Finset.subset_univ _), mem_edgesOf] at he he'
  obtain ⟨u, -, -, hu⟩ := (valid_edgeSet G).pair_of_mem (Finset.mem_univ e) he.2
  obtain ⟨u', -, -, hu'⟩ := (valid_edgeSet G).pair_of_mem (Finset.mem_univ e') he'.2
  simp only [edgeEnds] at hu hu'
  have h1 : M.Adj v u := by rw [← SimpleGraph.Subgraph.mem_edgeSet, ← hu]; exact he.1
  have h2 : M.Adj v u' := by rw [← SimpleGraph.Subgraph.mem_edgeSet, ← hu']; exact he'.1
  obtain ⟨w, -, huniq⟩ := hM (M.edge_vert h1)
  apply Subtype.ext
  rw [hu, hu', huniq u h1, huniq u' h2]
end MatchingPolytope
