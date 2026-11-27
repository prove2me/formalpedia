-- Prove2me | solution 1 for MatchingPolytope.chi_proj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:34:02.61259+00:00
-- url     : https://prove2.me/submissions/a0a77975-14ba-478f-a17b-8a5b8ae1dc65

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
public import Theorems.Thm_MatchingPolytope_mem_proj

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace MatchingPolytope
theorem _root_.solution (N : Finset (DEdge G)) (e : G.edgeSet) : chi (proj G N) e = chi N (Sum.inl e) := by
  unfold chi
  by_cases h : Sum.inl e ∈ N <;> simp [h, mem_proj]
end MatchingPolytope
