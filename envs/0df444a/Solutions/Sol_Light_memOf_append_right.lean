-- Prove2me | solution 1 for Light.memOf_append_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:09:32.002817+00:00
-- url     : https://prove2.me/submissions/54e4621f-34d8-43ac-90f7-13591b896e55

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor

set_option autoImplicit false
section
open Light
open ThreeSumApsp ThreeSumApsp.WordRam
namespace Light
theorem _root_.solution (l₁ l₂ : List ℤ) (a : ℕ) :
    memOf (l₁ ++ l₂) (l₁.length + a) = memOf l₂ a := by
  unfold memOf
  rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
end Light
