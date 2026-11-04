-- Prove2me | solution 1 for Light.Ends.keeping
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:26:45.580509+00:00
-- url     : https://prove2.me/submissions/80a95d4d-e5a6-4af7-ae06-753a81636b17

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Theorems.Thm_Light_Exec_loc_eq_of_notMem_assigns

set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Light
namespace Ends
theorem _root_.solution {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop}
    (h : Ends lim P d s σ T Q) :
    Ends lim P d s σ T fun σ' => Q σ' ∧ ∀ y ∉ s.assigns, σ'.loc y = σ.loc y := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he, hc, hq, fun _ hy => he.loc_eq_of_notMem_assigns hy⟩
end Ends
end Light
