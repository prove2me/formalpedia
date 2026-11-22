-- Prove2me | solution 1 for MatchingLogic.global_completeness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:45.454713+00:00
-- url     : https://prove2.me/submissions/bc5424df-e5c8-4590-aa81-d3cf7b7962ae

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_Localization
public import Definitions.Def_LeanPool_MatchingLogic_Composite
public import Definitions.Def_LeanPool_MatchingLogic_Completeness
public import Theorems.Thm_MatchingLogic_proof_theoretic_localization
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
    GlobalCons Γ φ ↔ Provable Γ φ := by
  exact (semantic_localization hΓ hφ).trans
    (proof_theoretic_localization hL hS hΓ hφ).symm
end MatchingLogic
