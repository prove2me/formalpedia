-- Prove2me | solution 1 for Light.seg_memOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:13:56.702201+00:00
-- url     : https://prove2.me/submissions/4365931e-e8e9-4e39-aab8-8ed2b729c63b

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor
import Theorems.Thm_Light_memOf_append_left
import Theorems.Thm_Light_memOf_append_right

set_option autoImplicit false
section
open Light
open ThreeSumApsp ThreeSumApsp.WordRam
namespace Light
theorem _root_.solution (l₁ l l₂ : List ℤ) : Seg (memOf (l₁ ++ l ++ l₂)) l₁.length l := by
  intro i hi
  rw [List.append_assoc, memOf_append_right, memOf_append_left _ hi]
  exact List.getD_eq_getElem _ _ hi
end Light
