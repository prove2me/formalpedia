-- Prove2me | solution 1 for Light.IndexAt.keep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:26:51.125569+00:00
-- url     : https://prove2.me/submissions/47155b30-5710-4ffe-a1e5-fadb1a5343f7

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
open Light.IndexAt
variable {l : List ℕ} {p : ℕ}
namespace Light.IndexAt
theorem _root_.solution (h : IndexAt μ a l N p top)
    (hs : SameOn (fun b => Inside a N b ∧ b < top) μ μ' := by
      ( try refine _root_.Light.SameOn.cell ?_
        intro x_p2m_4856426279979274271 hx_p2m_4856426279979274271
        first
        | ((  repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_15161316734853224794);
                  (try have := h_p2m_15161316734853224794 x_p2m_4856426279979274271 (by omega));
                  revert h_p2m_15161316734853224794)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
        |
          (simp [] at hx_p2m_4856426279979274271;
            ( repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_3816441691721880850);
                  (try have := h_p2m_3816441691721880850 x_p2m_4856426279979274271 (by omega));
                  revert h_p2m_3816441691721880850)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
        | ( ( repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_6100302973931978208);
                  (try have := h_p2m_6100302973931978208 x_p2m_4856426279979274271 (by omega));
                  revert h_p2m_6100302973931978208)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
            fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                        SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                        its condition K x does not follow from the hypotheses."))) :
    IndexAt μ' a l N p top :=
  { h with
    seg :=
      Seg.congr h.seg fun i hi =>
        hs _
          (by
            have := h.len
            have := h.below
            rw [List.length_map] at hi
            omega) }
end Light.IndexAt
