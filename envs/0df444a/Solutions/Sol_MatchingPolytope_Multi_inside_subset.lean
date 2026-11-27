-- Prove2me | solution 1 for MatchingPolytope.Multi.inside_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:19:20.385336+00:00
-- url     : https://prove2.me/submissions/16cb5789-ede5-4b4b-87bd-ca933e595af6

module
public import Mathlib
public import Definitions.Def_MatchingPolytope_Multigraph

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution (D : Finset E) (S : Finset V) : inside ends D S ⊆ D := by
  classical exact Finset.filter_subset _ _
end MatchingPolytope.Multi
