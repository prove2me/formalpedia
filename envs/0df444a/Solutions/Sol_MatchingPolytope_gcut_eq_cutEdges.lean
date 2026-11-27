-- Prove2me | solution 1 for MatchingPolytope.gcut_eq_cutEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:29:28.595379+00:00
-- url     : https://prove2.me/submissions/d9314e18-2ac0-4c25-ad1a-3f9ccc31896b

module
public import Definitions.Def_MatchingPolytope_Defs
public import Definitions.Def_MatchingPolytope_Induction
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace MatchingPolytope
theorem _root_.solution [DecidableEq V] (S : Finset V) :
    gcut (edgeEnds G) univ S = cutEdges G S := by
  ext e
  simp [gcut, cutEdges]
end MatchingPolytope
