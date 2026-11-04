-- Prove2me | solution 1 for Light.ArrayAt.read
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:11:31.5823+00:00
-- url     : https://prove2.me/submissions/54d54c05-e8ce-417e-ae59-2d1fc98cb822

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_ArrayAt
import Theorems.Thm_Light_ListAt_read
import Theorems.Thm_Light_ArrayAt_listAt
import Theorems.Thm_Light_SegN_read


set_option autoImplicit false
section
open Light
open ThreeSumApsp
variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}
open Light.ArrayAt
namespace Light.ArrayAt
theorem _root_.solution (h : ArrayAt μ a l N U top) (hi : i < N) : μ (a + i) = l.getD i 0 := h.listAt.read hi
end Light.ArrayAt
