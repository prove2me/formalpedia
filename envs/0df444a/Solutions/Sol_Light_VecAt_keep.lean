-- Prove2me | solution 1 for Light.VecAt.keep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:35:45.201205+00:00
-- url     : https://prove2.me/submissions/98aa49ed-29b7-4a08-8e34-cd806837c4ab

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
set_option autoImplicit false
public section
open Light
open ThreeSumApsp
variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}
namespace Light
namespace VecAt
theorem _root_.solution {t n : ℕ} {I : Fin t → Fin n} (h : VecAt μ a I)
    (hs : SameOn (Inside a t) μ μ' := by
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
    VecAt μ' a I := fun k => (hs _ ⟨by omega, by omega⟩).trans (h k)
end VecAt
end Light
