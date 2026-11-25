-- Prove2me | solution 1 for GlobalTheory.OrbitsInAffineOpens.of_locally_on_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:02:42.229919+00:00
-- url     : https://prove2.me/submissions/5448d609-3c64-4f20-80a4-b38cbc28ac48

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
theorem _root_.solution [Finite G] (ρ : G →* Aut X) (f : X ⟶ Y) (hf : ∀ g, (ρ g).hom ≫ f = f)
    (h : ∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧ FiniteSubsetsInAffineOpens (f ⁻¹ᵁ W)) :
    OrbitsInAffineOpens ρ := ⟨fun x ↦ by
  obtain ⟨W, hyW, hW⟩ := h (f x)
  have horb : ∀ g, (ρ g).hom x ∈ f ⁻¹ᵁ W := fun g ↦ by
    show f ((ρ g).hom x) ∈ W
    rw [← Scheme.Hom.comp_apply, hf g]
    exact hyW
  obtain ⟨V, hV, hsV⟩ := FiniteSubsetsInAffineOpens.exists_isAffineOpen (X := (f ⁻¹ᵁ W).toScheme)
    (Set.range fun g : G ↦ (⟨(ρ g).hom x, horb g⟩ : f ⁻¹ᵁ W)) (Set.finite_range _)
  refine ⟨(f ⁻¹ᵁ W).ι ''ᵁ V, hV.image_of_isOpenImmersion _, fun g ↦ ?_⟩
  exact ⟨_, hsV ⟨g, rfl⟩, rfl⟩⟩
end GlobalTheory.OrbitsInAffineOpens
