-- Prove2me | solution 1 for Light.MatAt.keep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:35:56.884585+00:00
-- url     : https://prove2.me/submissions/57549f7a-f3f2-42fa-872b-5e22136e040d

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
public import Theorems.Thm_Light_MatAt_congr
set_option autoImplicit false
public section
open Light
open ThreeSumApsp
variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}
namespace Light
namespace MatAt
theorem _root_.solution {n k : ℕ} {A : Matrix (Fin n) (Fin k) ℤ} (h : MatAt μ a A)
    (hs : SameOn (Inside a (n * k)) μ μ' := by
      ( try refine _root_.Light.SameOn.cell ?_
        intro x_p2m_18012199293970436122 hx_p2m_18012199293970436122
        first
        | ((  repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_10331794896191121659);
                  (try have := h_p2m_10331794896191121659 x_p2m_18012199293970436122 (by omega));
                  revert h_p2m_10331794896191121659)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
        |
          (simp [] at hx_p2m_18012199293970436122;
            ( repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_4850485832999446649);
                  (try have := h_p2m_4850485832999446649 x_p2m_18012199293970436122 (by omega));
                  revert h_p2m_4850485832999446649)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
        | ( ( repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_12411661073569084955);
                  (try have := h_p2m_12411661073569084955 x_p2m_18012199293970436122 (by omega));
                  revert h_p2m_12411661073569084955)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
            fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                        SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                        its condition K x does not follow from the hypotheses."))) :
    MatAt μ' a A :=
  h.congr fun b h₁ h₂ => hs b ⟨h₁, h₂⟩
end MatAt
end Light
