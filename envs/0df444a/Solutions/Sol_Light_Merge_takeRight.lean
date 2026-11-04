-- Prove2me | solution 1 for Light.Merge.takeRight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:27:28.146545+00:00
-- url     : https://prove2.me/submissions/fd0f845b-e787-41ec-aabb-63d28de4ae91

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Merge
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_SegN_snoc
import Theorems.Thm_Light_Seg_get
import Theorems.Thm_Light_Seg_snoc
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
open Light.Merge
variable {μ : ℕ → ℤ} {a b dst : ℕ} {l r : List ℤ} {i j : ℕ}
namespace Light.Merge
theorem _root_.solution (C : Pre lim μ a b dst l r) {σ : State} (h : Inv μ a b dst l r i j σ) (hj : j < r.length)
    (hm : (l.drop i).merge (r.drop j) = r[j] :: (l.drop i).merge (r.drop (j + 1))) :
    mergeTakeRight.Runs lim σ (Taken μ a b dst l r (i + j + 1)) :=
  by
  obtain ⟨μ', out, rfl, hi, -, same, hlen, seg, hout⟩ := h
  (obtain ⟨⟩ := _root_.id C)
  have hread : μ' (b + j) = r[j] := (same _ (by omega)).trans (C.segR.get hj)
  have haddr : ((dst : ℤ) + i + j).toNat = dst + out.length := by omega
  refine
    ⟨by (
        (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, mergeTakeRight] <;> omega), i, j + 1, by omega,
      Function.update μ' (dst + out.length) r[j], out ++ [r[j]], ?_, hi, hj, same.update ⟨by omega, by omega⟩ _, by
      simp only [List.length_append, List.length_singleton]; omega, seg.snoc _, by rw [← hout, hm]; simp⟩
  simp [mergeTakeRight, update_frame_setLocal, haddr, hread]
end Light.Merge
