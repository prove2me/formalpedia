-- Prove2me | solution 1 for MatchingPolytope.sum_chi_innerEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:32:58.251077+00:00
-- url     : https://prove2.me/submissions/1479247c-b523-4d89-b486-c0d55eaa8f9e

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
public import Theorems.Thm_MatchingPolytope_inside_eq_innerEdges
public import Theorems.Thm_MatchingPolytope_Multi_sum_chi_inside


set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace MatchingPolytope
theorem _root_.solution (M : Finset G.edgeSet) (S : Finset V) :
    ∑ e ∈ innerEdges G S, chi M e = ((inside (edgeEnds G) M S).card : ℝ) := by
  rw [← inside_eq_innerEdges, sum_chi_inside (Finset.subset_univ M)]
end MatchingPolytope
