-- Prove2me | solution 1 for MatchingLogic.globalCons_of_localCons_localize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:56.819174+00:00
-- url     : https://prove2.me/submissions/20d402e3-6837-49be-becc-8cb39a2d8247

module
public import Definitions.Def_LeanPool_MatchingLogic_Boxes
public import Mathlib.Data.Set.Basic
public import Definitions.Def_LeanPool_MatchingLogic_Localization
public import Theorems.Thm_MatchingLogic_satSet_localize_iff
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
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic
theorem _root_.solution {Γ : Set (Pattern S Var)}
    {φ : Pattern S Var} (h : LocalCons (localize Γ) φ) : GlobalCons Γ φ := by
  intro M hM ρ
  have hloc : M.SatSet (localize Γ) := (satSet_localize_iff M).2 hM
  apply Set.eq_univ_of_forall
  intro u
  apply h M ρ
  simp only [Model.denoteSet, Set.mem_iInter]
  intro ψ hψ
  rw [hloc ψ hψ ρ]
  exact Set.mem_univ u
end MatchingLogic
