-- Prove2me | solution 1 for MatchingPolytope.cutEdges_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:33:30.664906+00:00
-- url     : https://prove2.me/submissions/e82e5c46-51ae-4b43-9167-ff6f29cb8569

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
theorem _root_.solution : cutEdges G ∅ = ∅ := by
  ext e
  simp [cutEdges]
end MatchingPolytope
