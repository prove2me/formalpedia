-- Prove2me | solution 1 for MatchingPolytope.Multi.exists_neg_of_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:29:11.344453+00:00
-- url     : https://prove2.me/submissions/b8aa7ffc-808f-4864-932a-9ab13728870d

module
public import Definitions.Def_MatchingPolytope_Glue
public import Definitions.Def_MatchingPolytope_Induction
public import Theorems.Thm_MatchingPolytope_Multi_InHull_push
public import Theorems.Thm_MatchingPolytope_Multi_Valid_pair
public import Theorems.Thm_MatchingPolytope_Multi_mem_gcut_singleton


set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*} {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution (hV : Valid ends W F) {d : E → ℝ} (hd : Ker ends W F d) (hd0 : d ≠ 0) :
    ∃ e, d e < 0 := by
  by_contra h
  push Not at h
  apply hd0
  funext e
  by_cases he : e ∈ F
  · obtain ⟨a, b, -, ha, -, hab⟩ := hV.pair he
    have hsum := hd.2 a ha
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun e _ => h e)] at hsum
    exact hsum e ((mem_gcut_singleton hV subset_rfl).2 ⟨he, by simp [hab]⟩)
  · exact hd.1 e he
end MatchingPolytope.Multi
