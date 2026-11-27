-- Prove2me | solution 1 for MatchingPolytope.Multi.restr_mem_poly_shrink
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:27:11.116333+00:00
-- url     : https://prove2.me/submissions/1f13f584-6b78-4a67-b7a6-75d10dac2249

module
public import Definitions.Def_MatchingPolytope_Multigraph
public import Definitions.Def_MatchingPolytope_Shrink
public import Theorems.Thm_MatchingPolytope_Multi_filter_collapse_self
public import Theorems.Thm_MatchingPolytope_Multi_filter_collapse_other
public import Theorems.Thm_MatchingPolytope_Multi_filter_collapse_odd
public import Theorems.Thm_MatchingPolytope_Multi_sum_restr_gcut_shrink

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable [DecidableEq V]
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution (hV : Valid ends W F) {x : E → ℝ} (hx : x ∈ Poly ends W F)
    {R : Finset V} {r : V} (hRW : R ⊆ W) (hr : r ∈ R) (hRodd : Odd R.card)
    (htight : ∑ e ∈ gcut ends F R, x e = 1) :
    restr (shrinkF ends F R) x ∈ Poly (shrinkEnds ends R r) (shrinkW W R r) (shrinkF ends F R) := by
  obtain ⟨hx0, hx1, hx2, hx3⟩ := hx
  refine ⟨fun e he => by simp [restr, he], fun e => ?_, fun v hv => ?_, fun T hT hTodd => ?_⟩
  · simp only [restr]; split_ifs
    · exact hx1 e
    · exact le_rfl
  · rw [sum_restr_gcut_shrink hV]
    simp only [shrinkW, Finset.mem_insert, Finset.mem_sdiff] at hv
    rcases hv with rfl | ⟨hvW, hvR⟩
    · rw [filter_collapse_self hr hRW]; exact htight
    · rw [filter_collapse_other hr hvW hvR]; exact hx2 v hvW
  · rw [sum_restr_gcut_shrink hV]
    exact hx3 _ (Finset.filter_subset _ _) (filter_collapse_odd hr hRW hRodd hT hTodd)
end MatchingPolytope.Multi
