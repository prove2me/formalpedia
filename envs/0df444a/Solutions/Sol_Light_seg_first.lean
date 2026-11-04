-- Prove2me | solution 1 for Light.seg_first
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:59:17.370878+00:00
-- url     : https://prove2.me/submissions/3f9ca1a6-ed0a-4925-a90a-0473d5b766e7

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor
import Theorems.Thm_Light_seg_memOf
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.toNat_natCast_add_natCast



set_option autoImplicit false
section
open Light
open ThreeSumApsp ThreeSumApsp.WordRam
namespace Light
theorem _root_.solution (n : ℤ) (l₁ l₂ : List ℤ) : Seg (memOf (n :: (l₁ ++ l₂))) 1 l₁ := by
  simpa using seg_memOf [n] l₁ l₂
end Light
