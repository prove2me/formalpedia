-- Prove2me | solution 1 for Light.ArrayAt.keep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:26:49.84576+00:00
-- url     : https://prove2.me/submissions/aa2cd547-5b7b-40a2-a25d-5b90d7f01eac

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_ArrayAt
import Theorems.Thm_Light_ListAt_keep
import Theorems.Thm_Light_ArrayAt_listAt
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep
set_option autoImplicit false
section
open Light
open ThreeSumApsp
variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}
open Light.ArrayAt
namespace Light.ArrayAt
theorem _root_.solution (h : ArrayAt μ a l N U top)
    (hs : SameOn (fun b => Inside a N b ∧ b < top) μ μ' := by
      ( try refine _root_.Light.SameOn.cell ?_
        intro x_p2m_17167928071560346525 hx_p2m_17167928071560346525
        first
        | ((  repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_4856426279979274271);
                  (try have := h_p2m_4856426279979274271 x_p2m_17167928071560346525 (by omega));
                  revert h_p2m_4856426279979274271)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
        |
          (simp [] at hx_p2m_17167928071560346525;
            ( repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_12566650714491517558);
                  (try have := h_p2m_12566650714491517558 x_p2m_17167928071560346525 (by omega));
                  revert h_p2m_12566650714491517558)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
        | ( ( repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_6548655093517329893);
                  (try have := h_p2m_6548655093517329893 x_p2m_17167928071560346525 (by omega));
                  revert h_p2m_6548655093517329893)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
            fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                        SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                        its condition K x does not follow from the hypotheses."))) :
    ArrayAt μ' a l N U top :=
  { h with seg := (h.listAt.keep hs).seg }
end Light.ArrayAt
