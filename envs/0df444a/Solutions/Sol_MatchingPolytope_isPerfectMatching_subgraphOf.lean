-- Prove2me | solution 1 for MatchingPolytope.isPerfectMatching_subgraphOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:32:28.179274+00:00
-- url     : https://prove2.me/submissions/a6684322-7109-4c8d-a6d6-7c40a3eb33b0

module
public import Definitions.Def_MatchingPolytope_Defs
public import Definitions.Def_MatchingPolytope_Induction
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Theorems.Thm_MatchingPolytope_valid_edgeSet
public import Theorems.Thm_MatchingPolytope_Multi_Valid_pair_of_mem
public import Theorems.Thm_MatchingPolytope_Multi_mem_gcut_singleton


set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace MatchingPolytope
theorem _root_.solution {M : Finset G.edgeSet}
    (hM : IsPM (edgeEnds G) univ univ M) : (subgraphOf G M).IsPerfectMatching := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro v
  obtain ⟨e0, he0⟩ := Finset.card_eq_one.1 (hM.2 v (Finset.mem_univ v))
  have hmem : e0 ∈ gcut (edgeEnds G) M {v} := by rw [he0]; exact Finset.mem_singleton_self _
  rw [mem_gcut_singleton (valid_edgeSet G) hM.1] at hmem
  obtain ⟨he0M, hve0⟩ := hmem
  obtain ⟨w, -, -, hw⟩ := (valid_edgeSet G).pair_of_mem (Finset.mem_univ e0) hve0
  refine ⟨w, ⟨e0, he0M, hw⟩, fun w' hw' => ?_⟩
  obtain ⟨e, heM, he⟩ := hw'
  have : e ∈ gcut (edgeEnds G) M {v} := by
    rw [mem_gcut_singleton (valid_edgeSet G) hM.1]
    exact ⟨heM, by simp [edgeEnds, he]⟩
  rw [he0, Finset.mem_singleton] at this
  subst this
  simp only [edgeEnds] at hw
  rw [hw] at he
  exact (Sym2.congr_right.1 he).symm
end MatchingPolytope
