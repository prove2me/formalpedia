-- Prove2me | solution 1 for MatchingLogic.definedness_conservative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:26.679444+00:00
-- url     : https://prove2.me/submissions/2da5d6e7-42a5-4fcf-80ec-844ef07f487d

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_EntryPoints
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Definedness
public import Theorems.Thm_MatchingLogic_denote_emb
public import Theorems.Thm_MatchingLogic_expand_sat_definednessAxiom
public import Theorems.Thm_MatchingLogic_global_completeness_of_localCompleteness
public import Theorems.Thm_MatchingLogic_soundness


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic
theorem _root_.solution
    (hL : StrongLocalCompleteness S Var)
    {Γ : Set (Pattern S Var)} {φ : Pattern S Var}
    (hΓ : ∀ γ ∈ Γ, Closed γ) (hφ : Closed φ) (x : Var)
    (h : Provable (emb '' Γ ∪ {definednessAxiom (S := S) x}) (emb φ)) :
    Provable Γ φ := by
  apply (global_completeness_of_localCompleteness hL hΓ hφ).mp
  intro M hM
  have henriched : GlobalCons (emb '' Γ ∪ {definednessAxiom (S := S) x}) (emb φ) :=
    soundness _ _ h
  have htheory : (expand M).SatSet
      (emb '' Γ ∪ {definednessAxiom (S := S) x}) := by
    intro ψ hψ
    rcases hψ with hψ | hψ
    · obtain ⟨γ, hγ, rfl⟩ := hψ
      intro ρ
      change Var → M.carrier at ρ
      exact (denote_emb M ρ γ).trans (hM γ hγ ρ)
    · rw [Set.mem_singleton_iff] at hψ
      subst ψ
      exact expand_sat_definednessAxiom M x
  have hemb := henriched (expand M) htheory
  intro ρ
  exact (denote_emb M ρ φ).symm.trans (hemb ρ)
end MatchingLogic
