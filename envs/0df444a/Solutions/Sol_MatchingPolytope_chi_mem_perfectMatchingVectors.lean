-- Prove2me | solution 1 for MatchingPolytope.chi_mem_perfectMatchingVectors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:33:49.119074+00:00
-- url     : https://prove2.me/submissions/a04b1c84-7638-495d-9352-6580853372f7

module
public import Definitions.Def_MatchingPolytope_Defs
public import Definitions.Def_MatchingPolytope_Induction
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Theorems.Thm_MatchingPolytope_mem_edgeSet_subgraphOf
public import Theorems.Thm_MatchingPolytope_isPerfectMatching_subgraphOf

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace MatchingPolytope
theorem _root_.solution {M : Finset G.edgeSet}
    (hM : IsPM (edgeEnds G) univ univ M) : chi M ∈ perfectMatchingVectors G := by
  refine ⟨subgraphOf G M, isPerfectMatching_subgraphOf G hM, ?_⟩
  funext e
  unfold incidence chi
  by_cases h : e ∈ M <;> simp [h, mem_edgeSet_subgraphOf]
end MatchingPolytope
