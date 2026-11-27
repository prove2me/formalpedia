-- Prove2me | solution 1 for MatchingPolytope.inside_eq_innerEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:31:03.235089+00:00
-- url     : https://prove2.me/submissions/7a634b33-453e-4622-9772-a2c4e20e43ce

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
theorem _root_.solution (S : Finset V) : inside (edgeEnds G) univ S = innerEdges G S := by
  ext e
  simp [inside, innerEdges]
end MatchingPolytope
