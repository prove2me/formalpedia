-- Prove2me | solution 1 for MatchingLogic.semantic_localization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:30:33.902536+00:00
-- url     : https://prove2.me/submissions/422b537e-8847-4c4f-b29e-9460968d8bbc

module
public import Definitions.Def_LeanPool_MatchingLogic_DoubleCover
public import Definitions.Def_LeanPool_MatchingLogic_Localization
public import Definitions.Def_LeanPool_MatchingLogic_Locality
public import Definitions.Def_LeanPool_MatchingLogic_Composite
public import Theorems.Thm_P2M_MatchingLogic_semantic_localization_of_closed___79ca4e008704

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic
theorem _root_.solution {Γ : Set (Pattern S Var)} {φ : Pattern S Var}
    (hΓ : ∀ γ ∈ Γ, Closed γ) (_hφ : Closed φ) :
    GlobalCons Γ φ ↔ LocalCons (localize Γ) φ :=
  semantic_localization_of_closed_Γ hΓ
end MatchingLogic
