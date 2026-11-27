-- Prove2me | solution 1 for MatchingPolytope.Multi.IsPM.of_shrink
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:26:59.885275+00:00
-- url     : https://prove2.me/submissions/f0912d54-69b4-4727-b081-8742d0f3c0f5

module
public import Definitions.Def_MatchingPolytope_Multigraph
public import Definitions.Def_MatchingPolytope_Shrink
public import Theorems.Thm_MatchingPolytope_Multi_shrinkF_subset
public import Theorems.Thm_MatchingPolytope_Multi_shrinkF_of_subset
public import Theorems.Thm_MatchingPolytope_Multi_gcut_shrink
public import Theorems.Thm_MatchingPolytope_Multi_filter_collapse_self
public import Theorems.Thm_MatchingPolytope_Multi_filter_collapse_other

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable [DecidableEq V]
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
namespace IsPM
theorem _root_.solution (hV : Valid ends W F) {R : Finset V} {r : V} (hRW : R ⊆ W) (hr : r ∈ R)
    {M : Finset E} (hM : IsPM (shrinkEnds ends R r) (shrinkW W R r) (shrinkF ends F R) M) :
    M ⊆ shrinkF ends F R ∧ (gcut ends M R).card = 1 ∧
      ∀ v ∈ W, v ∉ R → (gcut ends M {v}).card = 1 := by
  have hMF : M ⊆ F := hM.1.trans (shrinkF_subset R)
  have key : ∀ T, gcut (shrinkEnds ends R r) M T =
      gcut ends M (W.filter fun u => collapse R r u ∈ T) := by
    intro T
    rw [← gcut_shrink hV hMF R r T, shrinkF_of_subset hM.1]
  refine ⟨hM.1, ?_, fun v hv hvR => ?_⟩
  · have := hM.2 r (Finset.mem_insert_self _ _)
    rwa [key, filter_collapse_self hr hRW] at this
  · have := hM.2 v (by simp [shrinkW, hv, hvR])
    rwa [key, filter_collapse_other hr hv hvR] at this
end IsPM
end MatchingPolytope.Multi
