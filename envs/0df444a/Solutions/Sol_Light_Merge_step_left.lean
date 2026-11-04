-- Prove2me | solution 1 for Light.Merge.step_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:26:39.280223+00:00
-- url     : https://prove2.me/submissions/54e3b174-9c1d-4415-91a9-f22722fabb66

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Merge
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
variable {l r : List ℤ} {i j : ℕ}
namespace Light.Merge
theorem _root_.solution (hi : i < l.length) (hj : j < r.length) (h : l[i] ≤ r[j]) :
    (l.drop i).merge (r.drop j) = l[i] :: (l.drop (i + 1)).merge (r.drop j) := by
  rw [List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hj, List.cons_merge_cons]
  simp [h]
end Light.Merge
