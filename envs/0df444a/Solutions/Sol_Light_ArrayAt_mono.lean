-- Prove2me | solution 1 for Light.ArrayAt.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:07:23.32207+00:00
-- url     : https://prove2.me/submissions/0da5da63-1de3-4e70-a5c4-a9fe56368ed5

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_ArrayAt
set_option autoImplicit false
section
open Light
open ThreeSumApsp
variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}
open Light.ArrayAt
namespace Light.ArrayAt
theorem _root_.solution (h : ArrayAt μ a l N U top)
    (hU : U ≤ U' := by
      first
      | omega
      | ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
    (ht : top ≤ top' := by
      first
      | omega
      | ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)) :
    ArrayAt μ a l N U' top' :=
  { h with bound := fun x hx => (h.bound x hx).trans hU, below := h.below.trans ht }
end Light.ArrayAt
