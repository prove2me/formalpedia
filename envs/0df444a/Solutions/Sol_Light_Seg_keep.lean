-- Prove2me | solution 1 for Light.Seg.keep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:33:54.761464+00:00
-- url     : https://prove2.me/submissions/f1c727d4-23be-43a3-abd4-3622f152f89f

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
public import Theorems.Thm_Light_Seg_congr
set_option autoImplicit false
public section
open Light
open ThreeSumApsp
variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}
namespace Light
namespace Seg
theorem _root_.solution (h : Seg μ a l)
    (hs : SameOn (Inside a l.length) μ μ' := by
      ( try refine _root_.Light.SameOn.cell ?_
        intro x_p2m_4247050351032278221 hx_p2m_4247050351032278221
        first
        | ((  repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_9451296152311787892);
                  (try have := h_p2m_9451296152311787892 x_p2m_4247050351032278221 (by omega));
                  revert h_p2m_9451296152311787892)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
        |
          (simp [] at hx_p2m_4247050351032278221;
            ( repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_15161316734853224794);
                  (try have := h_p2m_15161316734853224794 x_p2m_4247050351032278221 (by omega));
                  revert h_p2m_15161316734853224794)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
        | ( ( repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_3816441691721880850);
                  (try have := h_p2m_3816441691721880850 x_p2m_4247050351032278221 (by omega));
                  revert h_p2m_3816441691721880850)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
            fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                        SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                        its condition K x does not follow from the hypotheses."))) :
    Seg μ' a l :=
  h.congr fun i hi => hs _ ⟨by omega, by omega⟩
end Seg
end Light
