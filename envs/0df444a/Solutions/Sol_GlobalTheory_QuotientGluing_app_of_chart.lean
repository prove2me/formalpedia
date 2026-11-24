-- Prove2me | solution 1 for GlobalTheory.QuotientGluing.app_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:14:12.219456+00:00
-- url     : https://prove2.me/submissions/20c02445-0dfc-4b98-8715-ff14a2510493

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsInvariantSectionMemBasicOpenIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsQuotientOfFiniteGroup
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.QuotientGluing
variable {G : Type} [Group G] [Finite G] {X : Scheme.{0}}
omit [Finite G]
namespace GlobalTheory.QuotientGluing
theorem _root_.solution {T Y Y' : Scheme.{0}} {ρ : G →* Aut X} {σ : G →* Aut T}
    {q : T ⟶ Y'} (h : IsAffineQuotient σ q) (π : X ⟶ Y) (i : T ⟶ X) [IsOpenImmersion i]
    (hi : ∀ g, (σ g).hom ≫ i = i ≫ (ρ g).hom) (κ : Y' ⟶ Y) [IsOpenImmersion κ]
    (hκ : i ≫ π = q ≫ κ) (W : Y.Opens) (hW : W ≤ κ.opensRange) (hW' : π ⁻¹ᵁ W ≤ i.opensRange) :
    Function.Injective (π.app W) ∧
      ∀ s : Γ(X, π ⁻¹ᵁ W), IsInvariantSection ρ _ s → s ∈ Set.range (π.app W) := by
  have e : q ⁻¹ᵁ κ ⁻¹ᵁ W = i ⁻¹ᵁ π ⁻¹ᵁ W := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hκ]
  have h1 : IsIso (κ.app W) := κ.isIso_app W hW
  have h2 : IsIso (i.appLE (π ⁻¹ᵁ W) (q ⁻¹ᵁ κ ⁻¹ᵁ W) e.le) := by
    have := i.isIso_app _ hW'
    have : IsIso (homOfLE e.le) := homOfLE_isIso_of_eq _ e
    rw [Scheme.Hom.appLE]
    infer_instance
  have sq : π.app W ≫ i.appLE (π ⁻¹ᵁ W) (q ⁻¹ᵁ κ ⁻¹ᵁ W) e.le = κ.app W ≫ q.app _ := by
    simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, hκ]
  have sq' (r : Γ(Y, W)) : i.appLE (π ⁻¹ᵁ W) (q ⁻¹ᵁ κ ⁻¹ᵁ W) e.le (π.app W r) =
      q.app _ (κ.app W r) := by
    rw [← CommRingCat.comp_apply, sq, CommRingCat.comp_apply]
  have b1 := ConcreteCategory.bijective_of_isIso (κ.app W)
  have b2 := ConcreteCategory.bijective_of_isIso (i.appLE (π ⁻¹ᵁ W) (q ⁻¹ᵁ κ ⁻¹ᵁ W) e.le)
  refine ⟨fun a b hab ↦ b1.1 (h.app_injective _ ?_), fun s hs ↦ ?_⟩
  · rw [← sq', ← sq', hab]
  · obtain ⟨t, ht⟩ := h.mem_range_app (κ ⁻¹ᵁ W) _ (hs.appLE i hi (h.preimage_le _) e.le)
    obtain ⟨r, rfl⟩ := b1.2 t
    exact ⟨r, b2.1 ((sq' r).trans ht)⟩
end GlobalTheory.QuotientGluing
