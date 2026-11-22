-- Prove2me | solution 1 for MatchingLogic.BoxesControl.dia_position_visible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:16.657797+00:00
-- url     : https://prove2.me/submissions/b42bbfb0-1fad-4a2d-8702-1b6126631fe4

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



set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.BoxesControl
namespace MatchingLogic.BoxesControl
theorem _root_.solution :
    Mo.denote (fun _ => (2 : Fin 4)) (dia e0 (.var 0)) ≠
      Mo.denote (fun _ => (2 : Fin 4)) (dia e1 (.var (0 : Nat))) := by
  intro h
  have hmem : (1 : Fin 4) ∈
      Mo.denote (fun _ => (2 : Fin 4)) (dia e0 (.var 0)) := by
    change (1 : Fin 4) ∈ Mo.app ()
      (fun i => Mo.denote (fun _ => (2 : Fin 4))
        (if i = e0.2 then .var 0 else Pattern.tp))
    refine ⟨fun i => if i = 0 then 2 else 3, ?_, ?_⟩
    · intro i
      by_cases hi : i = 0
      · subst i
        simp
      · simp [hi]
    · simp [Mo]
  rw [h] at hmem
  change (1 : Fin 4) ∈ Mo.app ()
    (fun i => Mo.denote (fun _ => (2 : Fin 4))
      (if i = e1.2 then .var 0 else Pattern.tp)) at hmem
  rcases hmem with ⟨a, ha, hout⟩
  have ha1 : a 1 = 2 := by
    simpa [e1] using ha 1
  simp [Mo, ha1] at hout
end MatchingLogic.BoxesControl
