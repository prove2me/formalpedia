-- Prove2me | solution 1 for GlobalTheory.exists_isInvariantSection_basicOpen_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:37:27.095528+00:00
-- url     : https://prove2.me/submissions/a3c28ec7-7ed1-45ba-a9a6-f63d68e328dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsInvariantSectionMemBasicOpenIff
import Theorems.Thm_GlobalTheory_aut_map_one_apply
import Theorems.Thm_GlobalTheory_exists_isInvariantSection_mem_basicOpen_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {G : Type v} [Group G] {X Y : Scheme.{u}}
variable {ρ : G →* Aut X}
variable [Finite G]
namespace GlobalTheory
theorem _root_.solution {U : X.Opens} (hU : ∀ g, U ≤ (ρ g).hom ⁻¹ᵁ U)
    (s : Γ(X, U)) (hs : ∀ g, X.basicOpen s ≤ (ρ g).hom ⁻¹ᵁ X.basicOpen s) :
    ∃ t : Γ(X, U), IsInvariantSection ρ U t ∧ X.basicOpen t = X.basicOpen s := by
  obtain ⟨t, ht, hmem⟩ := exists_isInvariantSection_mem_basicOpen_iff hU s
  refine ⟨t, ht, le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)⟩
  · have := (hmem x).1 hx 1
    rwa [aut_map_one_apply] at this
  · exact (hmem x).2 fun g ↦ hs g hx
end GlobalTheory
