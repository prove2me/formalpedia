-- Prove2me | solution 1 for GlobalTheory.IsAffineQuotient.of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:29:35.342806+00:00
-- url     : https://prove2.me/submissions/ecf4f34e-5528-4bdb-a1a7-792fdb0f51e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {G : Type v} [Group G] {X Y Z : Scheme.{u}}
open GlobalTheory.IsAffineQuotient
variable {ρ : G →* Aut X} {π : X ⟶ Y}
namespace GlobalTheory.IsAffineQuotient
theorem _root_.solution [Finite G] (hπ : ∀ g, (ρ g).hom ≫ π = π)
    (h : ∀ y : Y, ∃ W : Y.Opens, IsAffineOpen W ∧ y ∈ W ∧ IsAffineOpen (π ⁻¹ᵁ W) ∧
      Function.Injective (π.app W) ∧
      ∀ s : Γ(X, π ⁻¹ᵁ W), IsInvariantSection ρ _ s → s ∈ Set.range (π.app W)) :
    IsAffineQuotient ρ π := by
  have : IsAffineHom π := isAffineHom_of_forall_exists_isAffineOpen π fun y ↦ by
    obtain ⟨W, h₁, h₂, h₃, -⟩ := h y
    exact ⟨W, h₂, h₁, h₃⟩
  have := isSchemeTheoreticallyDominant_of_cover π fun y ↦ by
    obtain ⟨W, h₁, h₂, -, h₃, -⟩ := h y
    exact ⟨W, h₁, h₂, h₃⟩
  refine ⟨hπ, ‹_›, π.app_injective, fun W s hs ↦ hs.mem_range_app_of_cover π hπ fun y ↦ ?_⟩
  obtain ⟨W, h₁, h₂, -, -, h₃⟩ := h y
  exact ⟨W, h₁, h₂, h₃⟩
end GlobalTheory.IsAffineQuotient
