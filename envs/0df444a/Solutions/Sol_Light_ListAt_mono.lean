-- Prove2me | solution 1 for Light.ListAt.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:07:22.293711+00:00
-- url     : https://prove2.me/submissions/27f0ac12-d17e-43d3-9342-7b5d3448cc06

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
theorem _root_.solution (h : ListAt μ a l N top)
    (ht : top ≤ top' := by
      first
      | omega
      | ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)) :
    ListAt μ a l N top' :=
  { h with below := h.below.trans ht }
end Light.ListAt
