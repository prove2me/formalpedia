-- Prove2me | solution 1 for GlobalTheory.quotient_flat_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:30:35.376165+00:00
-- url     : https://prove2.me/submissions/12cad17d-2645-4b03-8ac4-9291abfee30e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsActionOfIsPullback
import Theorems.Thm_GlobalTheory_exists_action_of_isPullback
import Theorems.Thm_GlobalTheory_IsAffineQuotient_of_isPullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' Y Y' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X') (φ : Y ⟶ Y') (p : Y ⟶ X) (p' : Y' ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsPullback φ p p' π → Flat p' → (∃ τ : Γ →* Aut Y, ∀ g, (τ g).hom ≫ φ = φ ∧ (τ g).hom ≫ p = p ≫ (ρ g).hom) ∧ ∀ τ : Γ →* Aut Y, (∀ g, (τ g).hom ≫ φ = φ ∧ (τ g).hom ≫ p = p ≫ (ρ g).hom) → (IsAffineHom φ ∧ (∀ g, (τ g).hom ≫ φ = φ) ∧ ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V), (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (φ.app V).hom) := by
  intro Γ _ _ X X' Y Y' ρ π φ p p' hq H hflat
  obtain ⟨hπa, hπ, hV⟩ := hq
  refine ⟨exists_action_of_isPullback ρ hπ H.flip, fun τ hτ => ?_⟩
  have hQ : IsAffineQuotient ρ π :=
    { comp_eq := hπ
      isAffineHom := hπa
      app_injective := fun W => (hV W).1
      mem_range_app := fun W s hs => (hV W).2 s (by
        unfold IsInvariantSection at hs
        intro g h
        obtain ⟨_, e⟩ := hs g
        exact e) }
  haveI := hflat
  have hB := hQ.of_isPullback H.flip (fun g => (hτ g).2) (fun g => (hτ g).1)
  exact ⟨hB.isAffineHom, hB.comp_eq, fun V => ⟨hB.app_injective V, fun f hf => hB.mem_range_app V f (by
    unfold IsInvariantSection
    intro g
    have hle : φ ⁻¹ᵁ V ≤ (τ g).hom ⁻¹ᵁ φ ⁻¹ᵁ V := by
      rw [← Scheme.Hom.comp_preimage, (hτ g).1]
    exact ⟨hle, hf g hle⟩)⟩⟩
end GlobalTheory
