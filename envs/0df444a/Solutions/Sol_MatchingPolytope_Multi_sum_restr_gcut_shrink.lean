-- Prove2me | solution 1 for MatchingPolytope.Multi.sum_restr_gcut_shrink
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:25:50.581685+00:00
-- url     : https://prove2.me/submissions/a0c3d786-abc9-4c83-ab5f-13f1ef309b48

module
public import Definitions.Def_MatchingPolytope_Multigraph
public import Definitions.Def_MatchingPolytope_Shrink
public import Theorems.Thm_MatchingPolytope_Multi_gcut_shrink
public import Theorems.Thm_MatchingPolytope_Multi_gcut_subset


set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable [DecidableEq V]
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution (hV : Valid ends W F) (R : Finset V) (r : V) (T : Finset V)
    (x : E → ℝ) :
    ∑ e ∈ gcut (shrinkEnds ends R r) (shrinkF ends F R) T, restr (shrinkF ends F R) x e =
      ∑ e ∈ gcut ends F (W.filter fun u => collapse R r u ∈ T), x e := by
  rw [← gcut_shrink hV subset_rfl R r T]
  apply Finset.sum_congr rfl
  intro e he
  simp [restr, gcut_subset _ _ he]
end MatchingPolytope.Multi
