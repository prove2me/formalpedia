-- Prove2me | solution 1 for MatchingLogic.SetVariables.set_variable_is_not_a_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:45:51.48679+00:00
-- url     : https://prove2.me/submissions/edfde1f6-4b0f-46ba-aae1-be8b0544a737

module
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_SetVariables
public import Theorems.Thm_MatchingLogic_SetVariables_sGlobalCons_svar_bot
public import Theorems.Thm_MatchingLogic_SetVariables_not_globalCons_const_bot

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.SetVariables
variable {S : Signature} {Var SVar : Type} [DecidableEq Var]
namespace MatchingLogic.SetVariables
theorem _root_.solution (X : SVar) :
    SGlobalCons (S := constSig) (Var := Var) {SPattern.svar X} SPattern.bot ∧
      ¬ GlobalCons (S := constSig) (Var := Var) {dPat} Pattern.bot := by
  exact ⟨sGlobalCons_svar_bot X, not_globalCons_const_bot⟩
end MatchingLogic.SetVariables
