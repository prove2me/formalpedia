-- Prove2me | solution 1 for MatchingLogic.denote_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:17:30.105839+00:00
-- url     : https://prove2.me/submissions/033c6ab9-b811-4ad1-9f44-056b11684552

module
public import Definitions.Def_LeanPool_MatchingLogic_Core
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_ex
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


attribute [local simp] MatchingLogic.FV_var
attribute [local simp] MatchingLogic.FV_bot
attribute [local simp] MatchingLogic.FV_imp
attribute [local simp] MatchingLogic.FV_app
attribute [local simp] MatchingLogic.FV_ex
section
@[expose] public section
namespace MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
private theorem denote_congr_induction (M : Model S) (φ : Pattern S Var) :
    ∀ (ρ ρ' : Var → M.carrier), (∀ x ∈ FV φ, ρ x = ρ' x) →
      M.denote ρ φ = M.denote ρ' φ := by
  induction φ with
  | var x =>
    intro ρ ρ' h
    simp only [denote_var]
    rw [h x (by simp)]
  | bot => simp
  | app σ f ih =>
    intro ρ ρ' h
    simp only [denote_app]
    congr 2
    funext i
    exact ih i ρ ρ' (fun x hx => h x (by
      simp only [FV_app, Set.mem_iUnion]
      exact ⟨i, hx⟩))
  | imp φ ψ ihφ ihψ =>
    intro ρ ρ' h
    simp only [denote_imp]
    rw [ihφ ρ ρ' (fun x hx => h x (Set.mem_union_left _ hx)),
        ihψ ρ ρ' (fun x hx => h x (Set.mem_union_right _ hx))]
  | ex x φ ih =>
    intro ρ ρ' h
    simp only [denote_ex]
    congr 1
    funext a
    apply ih (Function.update ρ x a) (Function.update ρ' x a)
    intro y hy
    by_cases hyx : y = x
    · subst y
      simp
    · simp only [Function.update_apply, if_neg hyx]
      exact h y ⟨hy, by simpa using hyx⟩
end MatchingLogic
end
end

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic
theorem _root_.solution (M : Model S) (φ : Pattern S Var) :
    ∀ (ρ ρ' : Var → M.carrier), (∀ x ∈ FV φ, ρ x = ρ' x) →
      M.denote ρ φ = M.denote ρ' φ :=
  denote_congr_induction M φ
end MatchingLogic
