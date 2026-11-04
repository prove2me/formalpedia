-- Prove2me | solution 1 for Light.ArrayAt.abs_read_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:56:30.153231+00:00
-- url     : https://prove2.me/submissions/a229e91c-9371-441c-a313-1c6f0d952b8e

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_ArrayAt
import Theorems.Thm_Light_SegN_getElem
import Theorems.Thm_ThreeSumApsp_AbsLe_getElem


set_option autoImplicit false
section
open Light
open ThreeSumApsp
variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}
open Light.ArrayAt
namespace Light.ArrayAt
theorem _root_.solution (h : ArrayAt μ a l N U top) (hi : i < N) : |μ (a + i)| ≤ U := by
  rw [h.seg i (h.len ▸ hi)]
  exact h.bound.getElem _
end Light.ArrayAt
