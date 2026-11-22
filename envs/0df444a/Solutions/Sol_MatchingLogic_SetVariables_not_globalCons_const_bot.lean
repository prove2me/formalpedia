-- Prove2me | solution 1 for MatchingLogic.SetVariables.not_globalCons_const_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:34:40.326834+00:00
-- url     : https://prove2.me/submissions/5d245c93-fa81-426d-be6a-fb21dd7fa9e8

module
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_SetVariables
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
attribute [local simp] MatchingLogic.FV_app
attribute [local simp] MatchingLogic.FV_bot
attribute [local simp] MatchingLogic.FV_ex
attribute [local simp] MatchingLogic.FV_imp
attribute [local simp] MatchingLogic.FV_var
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var



set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.SetVariables
variable {S : Signature} {Var SVar : Type} [DecidableEq Var]
namespace MatchingLogic.SetVariables
theorem _root_.solution :
    ¬ GlobalCons (S := constSig) (Var := Var) {dPat} Pattern.bot := by
  intro h
  have hd : fullConstModel.SatSet ({dPat} : Set (Pattern constSig Var)) := by
    intro φ hφ ρ
    have : φ = dPat := by simpa using hφ
    subst φ
    unfold Model.Total
    ext u
    simp [Model.denote, Model.app]
  have hbot := h fullConstModel hd (fun _ => ())
  unfold Model.Total at hbot
  exact Set.empty_ne_univ hbot
end MatchingLogic.SetVariables
