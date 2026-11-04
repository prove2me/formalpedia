-- Prove2me | solution 1 for Light.Meets.append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:33:39.926793+00:00
-- url     : https://prove2.me/submissions/3c3dc2f6-d092-4591-98d6-33fba3ae3c13

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
public import Theorems.Thm_Light_Ends_append
public import Theorems.Thm_Light_Exec_append
public import Theorems.Thm_P2M_Light_getElem__append_of_eq_some_9fa037aa12b5


set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}
namespace Light
namespace Meets
theorem _root_.solution (h : Meets lim P p d vals μ T R) (P' : Program) :
    Meets lim (P ++ P') p d vals μ T R := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, getElem?_append_of_eq_some hp P', he.append P'⟩
end Meets
end Light
