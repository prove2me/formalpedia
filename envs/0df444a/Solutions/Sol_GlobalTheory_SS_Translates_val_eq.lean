-- Prove2me | solution 1 for GlobalTheory.SS.Translates.val_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:20:36.639412+00:00
-- url     : https://prove2.me/submissions/d46f61f4-daa5-42a3-b2a9-edad7a88c571

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TranslationBySection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenImmersionOfSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_StrictModelTranslatesTwistCompatible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Translates
namespace GlobalTheory.SS.Translates
theorem _root_.solution {T X X₁ X₂ O₁ O₂ Y S : Scheme.{0}} (d : T ⟶ X) {z : X} (hz : z ∈ closure (Set.range d))
    (u₁ : X ⟶ X₁) (u₂ : X ⟶ X₂) (i₁ : O₁ ⟶ X₁) (i₂ : O₂ ⟶ X₂) [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    (p : O₁ ⟶ Y) (q : O₂ ⟶ Y) (π : Y ⟶ S) [IsSeparated π] (ρ₁ : X₁ ⟶ S) (ρ₂ : X₂ ⟶ S)
    (hp : p ≫ π = i₁ ≫ ρ₁) (hq : q ≫ π = i₂ ≫ ρ₂) (hu : u₁ ≫ ρ₁ = u₂ ≫ ρ₂)
    (h : ∀ (T' : Scheme.{0}) (a : T' ⟶ T) (t₁ : T' ⟶ O₁) (t₂ : T' ⟶ O₂), t₁ ≫ i₁ = a ≫ d ≫ u₁ →
      t₂ ≫ i₂ = a ≫ d ≫ u₂ → t₁ ≫ p = t₂ ≫ q)
    {o₁ : O₁} {o₂ : O₂} (h₁ : i₁ o₁ = u₁ z) (h₂ : i₂ o₂ = u₂ z) : p o₁ = q o₂ := by
  let O : X.Opens := u₁ ⁻¹ᵁ i₁.opensRange ⊓ u₂ ⁻¹ᵁ i₂.opensRange
  have r₁ : Set.range (O.ι ≫ u₁) ⊆ Set.range i₁ := by
    rintro _ ⟨x, rfl⟩; exact x.2.1
  have r₂ : Set.range (O.ι ≫ u₂) ⊆ Set.range i₂ := by
    rintro _ ⟨x, rfl⟩; exact x.2.2
  let l₁ := IsOpenImmersion.lift i₁ (O.ι ≫ u₁) r₁
  let l₂ := IsOpenImmersion.lift i₂ (O.ι ≫ u₂) r₂
  have e₁ : l₁ ≫ i₁ = O.ι ≫ u₁ := IsOpenImmersion.lift_fac _ _ _
  have e₂ : l₂ ≫ i₂ = O.ι ≫ u₂ := IsOpenImmersion.lift_fac _ _ _
  let o : O.toScheme := ⟨z, ⟨o₁, h₁⟩, ⟨o₂, h₂⟩⟩
  have f₁ : l₁ o = o₁ := i₁.isOpenEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, e₁, h₁]; rfl)
  have f₂ : l₂ o = o₂ := i₂.isOpenEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, e₂, h₂]; rfl)
  let P : Over.mk (O.ι ≫ u₁ ≫ ρ₁) ⟶ Over.mk π := Over.homMk (l₁ ≫ p) (by
    simp [hp, reassoc_of% e₁])
  let Q : Over.mk (O.ι ≫ u₁ ≫ ρ₁) ⟶ Over.mk π := Over.homMk (l₂ ≫ q) (by
    simp [hq, reassoc_of% e₂, hu])
  have : IsSeparated (Over.mk π).hom := ‹_›
  have hc : IsClosed (Set.range (equalizer.ι P Q).left) := (equalizer.ι P Q).left.isClosedEmbedding.isClosed_range
  have ho : o ∈ closure (Set.range (pullback.fst O.ι d)) := by
    rw [Scheme.Pullback.range_fst, ← O.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage O.ι.continuous]
    exact hz
  let t : Over.mk (pullback.fst O.ι d ≫ O.ι ≫ u₁ ≫ ρ₁) ⟶ Over.mk (O.ι ≫ u₁ ≫ ρ₁) := Over.homMk (pullback.fst O.ι d)
  have ht : t ≫ P = t ≫ Q := by
    ext1
    have := h _ (pullback.snd O.ι d) (pullback.fst O.ι d ≫ l₁) (pullback.fst O.ι d ≫ l₂)
      (by rw [Category.assoc, e₁, pullback.condition_assoc]) (by rw [Category.assoc, e₂, pullback.condition_assoc])
    simpa [t, P, Q] using this
  have hs : Set.range (pullback.fst O.ι d) ⊆ Set.range (equalizer.ι P Q).left := by
    rintro _ ⟨x, rfl⟩
    exact ⟨(equalizer.lift t ht).left x, congr(($(equalizer.lift_ι t ht)).left x)⟩
  obtain ⟨e, he⟩ := hc.closure_subset_iff.2 hs ho
  have := congr(($(equalizer.condition P Q)).left e)
  rw [← f₁, ← f₂, ← he]
  exact this
end GlobalTheory.SS.Translates
