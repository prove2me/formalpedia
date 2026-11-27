-- Prove2me | solution 1 for MatchingPolytope.card_gcut_proj_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:34:32.090645+00:00
-- url     : https://prove2.me/submissions/3206e239-dc1d-4105-93f6-df3825d45bdd

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
public import Theorems.Thm_MatchingPolytope_dValid
public import Theorems.Thm_MatchingPolytope_mem_proj
public import Theorems.Thm_MatchingPolytope_Multi_mem_gcut_singleton
public import Theorems.Thm_MatchingPolytope_valid_edgeSet


set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace MatchingPolytope
theorem _root_.solution {N : Finset (DEdge G)} (hN : IsPM (dEnds G) univ univ N) (v : V) :
    (gcut (edgeEnds G) (proj G N) {v}).card ≤ 1 := by
  rw [← hN.2 (Sum.inl v) (Finset.mem_univ _)]
  rw [← Finset.card_map ⟨Sum.inl, Sum.inl_injective⟩]
  apply Finset.card_le_card
  intro e' he'
  rw [Finset.mem_map] at he'
  obtain ⟨e, he, rfl⟩ := he'
  rw [mem_gcut_singleton (valid_edgeSet G) (Finset.subset_univ _), mem_proj] at he
  rw [mem_gcut_singleton (dValid G) (Finset.subset_univ _)]
  refine ⟨he.1, ?_⟩
  simp only [Function.Embedding.coeFn_mk, dEnds, Sym2.mem_map]
  exact ⟨v, he.2, rfl⟩
end MatchingPolytope
