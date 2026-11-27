-- Prove2me | solution 1 for MatchingPolytope.Multi.shrinkF_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:22:44.245601+00:00
-- url     : https://prove2.me/submissions/0f9c904a-33bf-4b72-8bdb-cf86327fd27d

module
public import Definitions.Def_MatchingPolytope_Multigraph
public import Definitions.Def_MatchingPolytope_Shrink
public import Theorems.Thm_MatchingPolytope_Multi_mem_shrinkF

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution (R : Finset V) : shrinkF ends F R ⊆ F := fun _ h => (mem_shrinkF.1 h).1
end MatchingPolytope.Multi
