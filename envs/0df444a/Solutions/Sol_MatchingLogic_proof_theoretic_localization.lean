-- Prove2me | solution 1 for MatchingLogic.proof_theoretic_localization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:09.445283+00:00
-- url     : https://prove2.me/submissions/9e307a32-ed04-446e-9942-0174e0accbbd

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_Localization
public import Definitions.Def_LeanPool_MatchingLogic_Composite
public import Definitions.Def_LeanPool_MatchingLogic_Completeness
public import Theorems.Thm_MatchingLogic_Provable_weaken_empty
public import Theorems.Thm_MatchingLogic_necessitation
public import Theorems.Thm_MatchingLogic_provable_conj
public import Theorems.Thm_MatchingLogic_semantic_localization


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic
theorem _root_.solution
    (hL : StrongLocalCompleteness S Var) (hS : Soundness S Var)
    {Γ : Set (Pattern S Var)} {φ : Pattern S Var}
    (hΓ : ∀ γ ∈ Γ, Closed γ) (hφ : Closed φ) :
    Provable Γ φ ↔ LocalCons (localize Γ) φ := by
  constructor
  · intro hprov
    exact (semantic_localization hΓ hφ).mp (hS Γ φ hprov)
  · intro hlocal
    obtain ⟨l, hl, himp⟩ := hL (localize Γ) φ hlocal
    have hconj : Provable Γ (conj l) := by
      apply provable_conj l
      intro δ hδ
      obtain ⟨γ, hγ, p, rfl⟩ := hl δ hδ
      exact necessitation (Provable.hyp hγ) p
    exact Provable.mp hconj himp.weaken_empty
end MatchingLogic
