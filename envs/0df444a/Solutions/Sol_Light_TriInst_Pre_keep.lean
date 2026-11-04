-- Prove2me | solution 1 for Light.TriInst.Pre.keep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:58:54.646714+00:00
-- url     : https://prove2.me/submissions/f4472a50-3ea3-4090-960d-f4412cc05f7a

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_ArrayAt
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_Submission_ThreeSumApsp_Util_Flag
import Definitions.Def_Submission_ThreeSumApsp_Programs_Tasks
import Theorems.Thm_Light_ArrayAt_keep
import Theorems.Thm_Light_IndexAt_keep
import Theorems.Thm_Light_ListAt_keep
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep
set_option autoImplicit false
section
open ThreeSumApsp
open Light
open ThreeSumApsp.Spec
namespace Light
namespace TriInst.Pre
theorem _root_.solution {x : TriInst} {μ μ' : ℕ → ℤ} {fr : ℕ} (h : x.Pre μ fr)
    (hs : Kept μ μ' fr := by
      ( try refine _root_.Light.SameOn.cell ?_
        intro x_p2m_10507305537187907905 hx_p2m_10507305537187907905
        first
        | ((  (repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_4247050351032278221);
                    (try have := h_p2m_4247050351032278221 x_p2m_10507305537187907905 (by omega));
                    revert h_p2m_4247050351032278221))
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
        |
          (simp [] at hx_p2m_10507305537187907905;
            ( (repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_4856426279979274271);
                    (try have := h_p2m_4856426279979274271 x_p2m_10507305537187907905 (by omega));
                    revert h_p2m_4856426279979274271))
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
        | ( ( (repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_12566650714491517558);
                    (try have := h_p2m_12566650714491517558 x_p2m_10507305537187907905 (by omega));
                    revert h_p2m_12566650714491517558))
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
            fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                        SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                        its condition K x does not follow from the hypotheses."))) :
    x.Pre μ' fr := by
  (obtain ⟨⟩ := _root_.id h)
  exact { h with segAB := h.segAB.keep, segBC := h.segBC.keep, segAC := h.segAC.keep }
end TriInst.Pre
end Light
