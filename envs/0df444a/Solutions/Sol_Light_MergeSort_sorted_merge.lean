-- Prove2me | solution 1 for Light.MergeSort.sorted_merge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:27:31.752937+00:00
-- url     : https://prove2.me/submissions/c2d96b39-2e80-4254-b87c-f0568457791e

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Merge
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_AbsLe_append
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast



set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program}
open Light.MergeSort
namespace Light.MergeSort
theorem _root_.solution {μ μ₁ μ₂ μ₃ μ₄ : ℕ → ℤ} {a fr h m : ℕ} {L S₁ S₂ : List ℤ} (hh : h ≤ L.length)
    (hP₁ : S₁.Perm (L.take h)) (hO₁ : S₁.Pairwise (· ≤ ·))
    (hk₁ : KeptBut μ μ₁ fr a (L.take h).length) (hP₂ : S₂.Perm (L.drop h))
    (hO₂ : S₂.Pairwise (· ≤ ·)) (hk₂ : KeptBut μ₁ μ₂ fr (a + h) (L.drop h).length)
    (hk₃ : SameOutside μ₂ μ₃ fr m) (hS₄ : Seg μ₄ a (S₁.merge S₂))
    (hk₄ : SameOutside μ₃ μ₄ a L.length) : Sorted μ a fr L μ₄ := by
  refine ⟨⟨S₁.merge S₂, hS₄, ?_, hO₁.merge hO₂⟩, fun c hc => ?_⟩
  · calc (S₁.merge S₂).Perm (S₁ ++ S₂) := List.merge_perm_append _
      _ |>.Perm (L.take h ++ L.drop h) := hP₁.append hP₂
      _ = L := List.take_append_drop h L
  · have hl₁ : (L.take h).length = h := by simp; omega
    have hl₂ : (L.drop h).length = L.length - h := by simp
    have := hc.2
    rw [hk₄ c hc.2, hk₃ c (Or.inl hc.1), hk₂ c ⟨hc.1, by omega⟩, hk₁ c ⟨hc.1, by omega⟩]
end Light.MergeSort
