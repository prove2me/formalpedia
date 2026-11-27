-- Prove2me | solution 1 for MatchingPolytope.Multi.shrinkF_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:23:05.317628+00:00
-- url     : https://prove2.me/submissions/a6a0679f-51e2-479c-8d2e-34895c7cbaa6

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
theorem _root_.solution {R : Finset V} {M : Finset E} (hM : M ⊆ shrinkF ends F R) :
    shrinkF ends M R = M := by
  ext e
  rw [mem_shrinkF]
  exact ⟨fun h => h.1, fun h => ⟨h, (mem_shrinkF.1 (hM h)).2⟩⟩
end MatchingPolytope.Multi
