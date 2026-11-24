-- Prove2me | solution 1 for GlobalTheory.OrbitsInAffineOpens.of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:46:31.964497+00:00
-- url     : https://prove2.me/submissions/0a2585b9-a320-4003-8763-87d4a83deefa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsInvariantSectionMemBasicOpenIff

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
open GlobalTheory.OrbitsInAffineOpens
namespace GlobalTheory.OrbitsInAffineOpens
theorem _root_.solution (ρ : G →* Aut X) (p : X ⟶ Y) [IsAffineHom p]
    (hp : ∀ g, (ρ g).hom ≫ p = p) : OrbitsInAffineOpens ρ := ⟨fun x ↦ by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top (p x))
  refine ⟨p ⁻¹ᵁ V, hV.preimage p, fun g ↦ ?_⟩
  show p ((ρ g).hom x) ∈ V
  rw [← Scheme.Hom.comp_apply, hp g]
  exact hxV⟩
end GlobalTheory.OrbitsInAffineOpens
