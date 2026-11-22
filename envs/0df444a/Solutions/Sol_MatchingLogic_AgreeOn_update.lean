-- Prove2me | solution 1 for MatchingLogic.AgreeOn.update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:15:34.582182+00:00
-- url     : https://prove2.me/submissions/67cb4c6f-a947-4b2c-9510-25e00a943c1b

module
public import Definitions.Def_LeanPool_MatchingLogic_Core
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Locality
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
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic
namespace AgreeOn
theorem _root_.solution {M : Model S} {C : Set M.carrier} {ρ ρ' : Var → M.carrier}
    (h : AgreeOn C ρ ρ') (x : Var) (a : M.carrier) :
    AgreeOn C (Function.update ρ x a) (Function.update ρ' x a) := by
  intro y
  rcases eq_or_ne y x with hy | hy
  · subst hy
    simp only [Function.update_apply]
    rcases Classical.em (a ∈ C) with ha | ha
    · exact Or.inl ⟨rfl, ha⟩
    · exact Or.inr ⟨ha, ha⟩
  · simp only [Function.update_apply, if_neg hy]
    exact h y
end AgreeOn
end MatchingLogic
