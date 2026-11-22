-- Prove2me | solution 1 for MatchingLogic.localCons_renameInjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:23:26.728806+00:00
-- url     : https://prove2.me/submissions/1774a679-046a-47e4-9bfb-9784e6b85ee9

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
public import Theorems.Thm_MatchingLogic_Pattern_rename_id
public import Theorems.Thm_MatchingLogic_Pattern_rename_comp
public import Theorems.Thm_MatchingLogic_Model_denote_renameInjective
public import Theorems.Thm_MatchingLogic_Model_denoteSet_renameInjective
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


attribute [local simp] MatchingLogic.Pattern.rename_id
attribute [local simp] MatchingLogic.Pattern.rename_comp

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}
namespace MatchingLogic
theorem _root_.solution [DecidableEq Var] [DecidableEq Var']
    (f : Var → Var') (hf : Function.Injective f)
    {Delta : Set (Pattern S Var)} {phi : Pattern S Var} :
    LocalCons Delta phi ↔
      LocalCons (Pattern.rename f '' Delta) (phi.rename f) := by
  constructor
  · intro h M rho
    rw [M.denoteSet_renameInjective f hf, M.denote_renameInjective f hf]
    exact h M (rho ∘ f)
  · intro h M rho
    classical
    let rho' : Var' → M.carrier :=
      Function.extend f rho (fun _ => Classical.choice M.nonempty)
    have hrho : rho' ∘ f = rho := by
      funext x
      exact hf.extend_apply rho (fun _ => Classical.choice M.nonempty) x
    have h' := h M rho'
    rw [M.denoteSet_renameInjective f hf, M.denote_renameInjective f hf] at h'
    simpa only [hrho] using h'
end MatchingLogic
