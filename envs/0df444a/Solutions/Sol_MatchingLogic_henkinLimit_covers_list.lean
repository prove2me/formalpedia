-- Prove2me | solution 1 for MatchingLogic.henkinLimit_covers_list
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:30:18.316929+00:00
-- url     : https://prove2.me/submissions/079ce7dd-411b-406e-92a4-39df12d98989

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Mathlib.Data.Countable.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Lindenbaum
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Theorems.Thm_MatchingLogic_henkinStages_mono
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_LocProvable_mp
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
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatWitnessed
namespace MatchingLogic
theorem _root_.solution {α : Type} (stageTheory : List α → Set α)
    (step : List α → α → List α) (enum : Nat → α) (base l : List α)
    (hstep : ∀ stage phi, stageTheory stage ⊆ stageTheory (step stage phi))
    (hl : ∀ q ∈ l, q ∈ henkinLimit stageTheory step enum base) :
    ∃ n, ∀ q ∈ l, q ∈ stageTheory (henkinStages step enum base n) := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons q l ih =>
      rcases hl q (by simp) with ⟨n, hn⟩
      obtain ⟨m, hm⟩ := ih (by
        intro r hr
        exact hl r (by simp [hr]))
      refine ⟨max n m, ?_⟩
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact henkinStages_mono stageTheory step enum base hstep
          (Nat.le_max_left n m) hn
      · exact henkinStages_mono stageTheory step enum base hstep
          (Nat.le_max_right n m) (hm r hr)
end MatchingLogic
