-- Prove2me | solution 1 for MatchingPolytope.isPM_edgesOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:32:24.319064+00:00
-- url     : https://prove2.me/submissions/934ab3a0-adac-40f3-b120-3b6eb738ba56

module
public import Definitions.Def_MatchingPolytope_Defs
public import Definitions.Def_MatchingPolytope_Induction
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Theorems.Thm_MatchingPolytope_valid_edgeSet
public import Theorems.Thm_MatchingPolytope_mem_edgesOf
public import Theorems.Thm_MatchingPolytope_Multi_Valid_pair_of_mem
public import Theorems.Thm_MatchingPolytope_Multi_mem_gcut_singleton


set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace MatchingPolytope
theorem _root_.solution {M : G.Subgraph} (hM : M.IsPerfectMatching) :
    IsPM (edgeEnds G) univ univ (edgesOf G M) := by
  refine ⟨Finset.subset_univ _, fun v _ => ?_⟩
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff] at hM
  obtain ⟨w, hw, huniq⟩ := hM v
  have hvw : G.Adj v w := M.adj_sub hw
  rw [Finset.card_eq_one]
  refine ⟨⟨s(v, w), (SimpleGraph.mem_edgeSet G).2 hvw⟩, ?_⟩
  ext e
  rw [mem_gcut_singleton (valid_edgeSet G) (Finset.subset_univ _), mem_edgesOf,
    Finset.mem_singleton]
  constructor
  · rintro ⟨he, hve⟩
    obtain ⟨u, -, -, hu⟩ := (valid_edgeSet G).pair_of_mem (Finset.mem_univ e) hve
    simp only [edgeEnds] at hu
    rw [hu, SimpleGraph.Subgraph.mem_edgeSet] at he
    have := huniq u he
    apply Subtype.ext
    simp only [hu, this]
  · rintro rfl
    simp only [edgeEnds, SimpleGraph.Subgraph.mem_edgeSet, Sym2.mem_iff, true_or, and_true]
    exact hw
end MatchingPolytope
