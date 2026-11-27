-- Prove2me | solution 1 for MatchingPolytope.Multi.gcut_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:20:55.557797+00:00
-- url     : https://prove2.me/submissions/36d09999-f4b9-4aae-b9c3-1fd997d90fdf

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
theorem _root_.solution {D D' : Finset E} (h : D ⊆ D') (S : Finset V) : gcut ends D S ⊆ gcut ends D' S := by
  classical exact Finset.filter_subset_filter _ h
end MatchingPolytope.Multi
