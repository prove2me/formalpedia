-- Prove2me | solution 1 for Light.ListAt.keep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:13:14.270558+00:00
-- url     : https://prove2.me/submissions/487cd4e2-31ee-4eed-96f8-b230cb3a15fc

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_ArrayAt
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
set_option autoImplicit false
section
open Light
open ThreeSumApsp
variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}
open Light.ListAt
namespace Light.ListAt
theorem _root_.solution (h : ListAt μ a l N top)
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
    ListAt μ' a l N top :=
  { h with seg := h.seg.congr fun i hi => hs _ (by have := h.len; have := h.below; omega) }
end Light.ListAt
