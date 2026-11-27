-- Prove2me | solution 1 for MatchingPolytope.mem_proj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:31:51.151873+00:00
-- url     : https://prove2.me/submissions/c452d514-9f09-421b-851b-52a5ae0407f4

module
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace MatchingPolytope
theorem _root_.solution {N : Finset (DEdge G)} {e : G.edgeSet} : e ∈ proj G N ↔ Sum.inl e ∈ N := by
  classical
  simp [proj]
end MatchingPolytope
