-- Prove2me | solution 1 for Light.SegN.keep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:34:56.010786+00:00
-- url     : https://prove2.me/submissions/2c46cc3f-3a72-47ac-b2a9-860e756dcd28

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Regions
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index
public import Definitions.Def_Submission_ThreeSumApsp_Util_List
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Tactic.Positivity
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
public import Theorems.Thm_Light_Seg_keep
public import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
public section
open Light
open ThreeSumApsp
variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}
namespace Light
namespace SegN
theorem _root_.solution {l : List ℕ} (h : SegN μ a l)
    (hs : SameOn (Inside a l.length) μ μ' := by
      ( try refine _root_.Light.SameOn.cell ?_
        intro x_p2m_8345441044875591925 hx_p2m_8345441044875591925
        first
        | ((  repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_17167928071560346525);
                  (try have := h_p2m_17167928071560346525 x_p2m_8345441044875591925 (by omega));
                  revert h_p2m_17167928071560346525)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
        |
          (simp [] at hx_p2m_8345441044875591925;
            ( repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_10331794896191121659);
                  (try have := h_p2m_10331794896191121659 x_p2m_8345441044875591925 (by omega));
                  revert h_p2m_10331794896191121659)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
        | ( ( repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_4850485832999446649);
                  (try have := h_p2m_4850485832999446649 x_p2m_8345441044875591925 (by omega));
                  revert h_p2m_4850485832999446649)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
            fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                        SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                        its condition K x does not follow from the hypotheses."))) :
    SegN μ' a l :=
  Seg.keep h (by simpa using hs)
end SegN
end Light
