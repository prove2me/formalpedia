-- Prove2me | solution 1 for MatchingLogic.SetVariables.sGlobalCons_svar_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:18.335405+00:00
-- url     : https://prove2.me/submissions/64b22b47-7c47-47eb-a806-e5bbb461ef68

module
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_SetVariables
public import Theorems.Thm_MatchingLogic_SetVariables_not_ssat_svar
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
theorem _root_.solution (X : SVar) :
    SGlobalCons (S := S) (Var := Var) {SPattern.svar X} SPattern.bot := by
  intro M hM
  exact (not_ssat_svar M X (hM (.svar X) (by simp))).elim
end MatchingLogic.SetVariables
