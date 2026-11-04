-- Prove2me | solution 1 for Light.ListAt.drop_take
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:07:13.916929+00:00
-- url     : https://prove2.me/submissions/4e00af7f-4b5d-46bc-b3ca-94808da3f333

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_ArrayAt

set_option autoImplicit false
section
open Light
open ThreeSumApsp
variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}
open Light.ListAt
namespace Light.ListAt
theorem _root_.solution (h : ListAt μ a l N top) (hk : k + n ≤ N) :
    ListAt μ (a + k) ((l.drop k).take n) n top where
  len := by rw [List.length_take, List.length_drop, h.len]; omega
  seg := (h.seg.drop k).take n
  below := by have := h.below; omega
end Light.ListAt
