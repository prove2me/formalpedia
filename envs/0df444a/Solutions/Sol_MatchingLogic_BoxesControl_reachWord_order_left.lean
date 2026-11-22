-- Prove2me | solution 1 for MatchingLogic.BoxesControl.reachWord_order_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:19.884225+00:00
-- url     : https://prove2.me/submissions/8ba4feff-60a4-4ca5-a94d-bf522a36c6c5

module
public import Definitions.Def_LeanPool_MatchingLogic_Boxes
public import Mathlib.Logic.IsEmpty.Defs
public import Mathlib.Order.BooleanAlgebra.Set
public import Definitions.Def_LeanPool_MatchingLogic_BoxesControl
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_boxes_cons
public import Theorems.Thm_MatchingLogic_boxes_nil
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
attribute [local simp] MatchingLogic.FV_app
attribute [local simp] MatchingLogic.FV_bot
attribute [local simp] MatchingLogic.FV_box
attribute [local simp] MatchingLogic.FV_boxes
attribute [local simp] MatchingLogic.FV_dia
attribute [local simp] MatchingLogic.FV_ex
attribute [local simp] MatchingLogic.FV_imp
attribute [local simp] MatchingLogic.FV_var
attribute [local simp] MatchingLogic.Model.reachWord_cons
attribute [local simp] MatchingLogic.Model.reachWord_nil
attribute [local simp] MatchingLogic.boxes_cons
attribute [local simp] MatchingLogic.boxes_nil
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var


section
@[expose] public section
namespace MatchingLogic
namespace BoxesControl
private theorem stepAt_e0_zero (v : Fin 4) : Mo.stepAt e0 0 v ↔ v = 1 := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    by_cases h : a 0 = 1 ∧ a 1 = 1
    · exact h.1
    · simp [Mo, h] at ha
  · rintro rfl
    refine ⟨fun _ => 1, ?_, rfl⟩
    simp [Mo]
private theorem stepAt_e1_one (v : Fin 4) : Mo.stepAt e1 1 v ↔ v = 3 := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    by_cases h : a 0 = 1 ∧ a 1 = 1
    · simp [Mo, h] at ha
    · by_cases h' : a 0 = 2 ∧ a 1 = 3
      · exact h'.2
      · simp [Mo, h, h'] at ha
  · rintro rfl
    refine ⟨fun i => if i = 0 then 2 else 3, ?_, rfl⟩
    simp [Mo]
end BoxesControl
end MatchingLogic
end
end

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.BoxesControl
namespace MatchingLogic.BoxesControl
theorem _root_.solution (v : Fin 4) :
    Mo.reachWord [e0, e1] 0 v ↔ v = 3 := by
  simp only [Model.reachWord_cons, Model.reachWord_nil]
  simp [stepAt_e0_zero, stepAt_e1_one]
end MatchingLogic.BoxesControl
