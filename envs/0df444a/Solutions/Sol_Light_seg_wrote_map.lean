-- Prove2me | solution 1 for Light.seg_wrote_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:37:13.901621+00:00
-- url     : https://prove2.me/submissions/3b592223-4a30-45bc-8b20-d1a477341fa2

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Pass
public import Theorems.Thm_Light_seg_wrote
public import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.toNat_natCast_add_natCast



set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
variable {μ : ℕ → ℤ} {dst j : ℕ} {f : ℕ → ℤ}
namespace Light
theorem _root_.solution (g : ℤ → ℤ) (L : List ℤ) :
    Seg (wrote μ dst (fun i => g (L.getD i 0)) L.length) dst (L.map g) :=
  seg_wrote (List.length_map g) fun i hi => by
    rw [List.getElem_map, List.getD_eq_getElem _ _ (by simpa using hi)]
end Light
