-- Prove2me | solution 1 for MatchingPolytope.Multi.shrinkEnds_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:21:55.790096+00:00
-- url     : https://prove2.me/submissions/17fa89ab-56fb-46ad-a6ef-c0b671f639e6

module
public import Definitions.Def_MatchingPolytope_Multigraph
public import Definitions.Def_MatchingPolytope_Shrink

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable [DecidableEq V]
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution {R : Finset V} {r : V} {e : E} {a b : V} (h : ends e = s(a, b)) :
    shrinkEnds ends R r e = s(collapse R r a, collapse R r b) := by
  simp [shrinkEnds, h]
end MatchingPolytope.Multi
