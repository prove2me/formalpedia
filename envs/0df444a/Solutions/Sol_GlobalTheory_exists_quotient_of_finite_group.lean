-- Prove2me | solution 1 for GlobalTheory.exists_quotient_of_finite_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:53:30.20344+00:00
-- url     : https://prove2.me/submissions/af308482-48cb-4ed7-8dcc-fb46ea64f2ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsInvariantSectionMemBasicOpenIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsQuotientOfFiniteGroup
import Theorems.Thm_GlobalTheory_QuotientGluing_exists_isAffineQuotient

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
theorem _root_.solution : ∀ (Γ : Type) [Group Γ] [Finite Γ] (X : Scheme.{0}) [X.IsSeparated] (ρ : Γ →* Aut X), (∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ g, (ρ g).hom x ∈ U) → ∃ (X' : Scheme.{0}) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) := by
  intro Γ _ _ X _ ρ h
  have : OrbitsInAffineOpens ρ := ⟨h⟩
  obtain ⟨X', π, hπ⟩ := QuotientGluing.exists_isAffineQuotient ρ
  exact ⟨X', π, hπ.isAffineHom, hπ.comp_eq, fun V ↦ ⟨hπ.app_injective V, fun f hf ↦
    hπ.mem_range_app V f fun g ↦ ⟨hπ.preimage_le V g, hf g _⟩⟩⟩
end GlobalTheory
