-- Prove2me | solution 1 for Light.ArrayAt.drop_take
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:56:31.315711+00:00
-- url     : https://prove2.me/submissions/e364be79-7e69-4c53-954e-edfcf0141f8e

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_ArrayAt
import Theorems.Thm_Light_ListAt_drop_take
import Theorems.Thm_Light_ArrayAt_listAt
import Theorems.Thm_Light_SegN_drop_take


set_option autoImplicit false
section
open Light
open ThreeSumApsp
variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}
open Light.ArrayAt
namespace Light.ArrayAt
theorem _root_.solution (h : ArrayAt μ a l N U top) (hk : k + n ≤ N) :
    ArrayAt μ (a + k) ((l.drop k).take n) n U top :=
  { h.listAt.drop_take hk with
    bound := fun x hx => h.bound x (List.mem_of_mem_drop (List.mem_of_mem_take hx)) }
end Light.ArrayAt
