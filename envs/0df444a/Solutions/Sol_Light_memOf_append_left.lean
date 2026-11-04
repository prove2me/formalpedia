-- Prove2me | solution 1 for Light.memOf_append_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:09:30.641197+00:00
-- url     : https://prove2.me/submissions/23bd902a-a617-4a60-bb3e-1dd9433f223b

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor

set_option autoImplicit false
section
open Light
open ThreeSumApsp ThreeSumApsp.WordRam
namespace Light
theorem _root_.solution {l₁ : List ℤ} (l₂ : List ℤ) {a : ℕ} (h : a < l₁.length) :
    memOf (l₁ ++ l₂) a = memOf l₁ a := by
  unfold memOf
  rw [List.getD_append _ _ _ _ h]
end Light
