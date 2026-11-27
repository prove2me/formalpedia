-- Prove2me | solution 1 for MatchingPolytope.Multi.gcut_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:28:08.579666+00:00
-- url     : https://prove2.me/submissions/db63f31c-e8ad-4ab1-a01b-15587ee448ff

module
public import Definitions.Def_MatchingPolytope_Shrink
public import Definitions.Def_MatchingPolytope_Glue

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution [DecidableEq E] (M N : Finset E) (T : Finset V) :
    gcut ends (M ∪ N) T = gcut ends M T ∪ gcut ends N T := by
  classical
  ext e
  simp [gcut, or_and_right]
end MatchingPolytope.Multi
