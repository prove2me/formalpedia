-- Prove2me | solution 1 for MatchingLogic.Necessity.agree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:34:17.627006+00:00
-- url     : https://prove2.me/submissions/cb09635b-6df7-49c7-8904-507965713d73

module
public import Definitions.Def_LeanPool_MatchingLogic_Locality
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Necessity
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var



set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Necessity
variable {Var : Type} [DecidableEq Var]
omit [DecidableEq Var]
namespace MatchingLogic.Necessity
theorem _root_.solution : AgreeOn (M := M) C (rho (Var := Var)) rho' := by
  intro _
  refine Or.inr ⟨?_, ?_⟩ <;> simp [rho, rho']
end MatchingLogic.Necessity
