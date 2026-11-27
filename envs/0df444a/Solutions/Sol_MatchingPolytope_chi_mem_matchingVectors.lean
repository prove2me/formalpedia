-- Prove2me | solution 1 for MatchingPolytope.chi_mem_matchingVectors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:34:12.896846+00:00
-- url     : https://prove2.me/submissions/c07eaf72-b388-49c9-adb3-b4437549a05e

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
public import Theorems.Thm_MatchingPolytope_mem_edgeSet_matchingSubgraphOf
public import Theorems.Thm_MatchingPolytope_isMatching_matchingSubgraphOf

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {V : Type*} (G : SimpleGraph V)
namespace MatchingPolytope
theorem _root_.solution {M : Finset G.edgeSet}
    (hM : ∀ v, (gcut (edgeEnds G) M {v}).card ≤ 1) : chi M ∈ matchingVectors G := by
  refine ⟨matchingSubgraphOf G M, isMatching_matchingSubgraphOf G hM, ?_⟩
  funext e
  unfold incidence chi
  by_cases h : e ∈ M <;> simp [h, mem_edgeSet_matchingSubgraphOf]
end MatchingPolytope
