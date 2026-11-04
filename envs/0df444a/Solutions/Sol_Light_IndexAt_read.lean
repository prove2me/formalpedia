-- Prove2me | solution 1 for Light.IndexAt.read
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:56:54.427132+00:00
-- url     : https://prove2.me/submissions/960101c4-d40a-4b99-a3f6-c6cb9ab505c7

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_ArrayAt
import Theorems.Thm_Light_ListAt_read
import Theorems.Thm_Light_ArrayAt_read
import Theorems.Thm_Light_SegN_read


set_option autoImplicit false
section
open Light
open ThreeSumApsp
variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}
open Light.IndexAt
variable {l : List ℕ} {p : ℕ}
namespace Light.IndexAt
theorem _root_.solution (h : IndexAt μ a l N p top) (hi : i < N) : μ (a + i) = (l.getD i 0 : ℕ) :=
  h.seg.read (h.len ▸ hi)
end Light.IndexAt
