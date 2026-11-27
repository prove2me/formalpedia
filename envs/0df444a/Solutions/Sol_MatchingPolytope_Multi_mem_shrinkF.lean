-- Prove2me | solution 1 for MatchingPolytope.Multi.mem_shrinkF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:21:46.567076+00:00
-- url     : https://prove2.me/submissions/a10df988-3950-4f43-be02-588c701388d6

module
public import Definitions.Def_MatchingPolytope_Multigraph
public import Definitions.Def_MatchingPolytope_Shrink

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution {R : Finset V} {e : E} :
    e ∈ shrinkF ends F R ↔ e ∈ F ∧ ∃ u ∈ ends e, u ∉ R := by
  classical
  simp [shrinkF]
end MatchingPolytope.Multi
