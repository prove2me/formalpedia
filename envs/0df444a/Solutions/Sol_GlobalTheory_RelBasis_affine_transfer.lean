-- Prove2me | solution 1 for GlobalTheory.RelBasis.affine_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:18:01.382054+00:00
-- url     : https://prove2.me/submissions/22b87e22-f969-44d2-ae02-113819b1f314

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IndepOnEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_PullbackSectionsBasisAffineBaseChangeOfAffine
import Theorems.Thm_GlobalTheory_RelBasis_affine_gs_appLE
import Theorems.Thm_GlobalTheory_RelBasis_affine_comb
import Theorems.Thm_GlobalTheory_RelBasis_gs_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.RelBasis
variable {X Y T Y' T' : Scheme.{0}} {L : LB X} {t : ℤ} {N : ℕ}
namespace GlobalTheory.RelBasis
theorem _root_.solution (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens)
    (j : Y' ⟶ Y) (p₁' : Y' ⟶ T') (g : T' ⟶ T) [IsOpenImmersion g] (sq : IsPullback j p₁' p₁ g)
    (hr : Set.range g = W) (e : ⊤ ≤ g ⁻¹ᵁ W) (hb : Function.Bijective (g.appLE W ⊤ e).hom)
    (h₁ : IndepOn b p₁' (j ≫ p₂) ⊤) (h₂ : SpanOn b p₁' (j ≫ p₂) ⊤) :
    IndepOn b p₁ p₂ W ∧ SpanOn b p₁ p₂ W := by
  have hj : IsOpenImmersion j := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq.flip inferInstance
  have hW : ∀ z : Y', p₁ (j z) ∈ W := fun z => by
    have : (j ≫ p₁) z ∈ W := by rw [sq.w]; exact e (show p₁' z ∈ (⊤ : T'.Opens) from trivial)
    exact this
  refine ⟨fun c hc => ?_, fun σ hσ => ?_⟩
  · have := h₁ (fun k => (g.appLE W ⊤ e).hom (c k)) (fun z i _ hz => by
      rw [affine_comb b p₁ p₂ W j p₁' g sq.w e c z i hz, hc (j z) i (hW z) hz, map_zero])
    funext k
    apply hb.1
    rw [Pi.zero_apply, map_zero]
    exact congrFun this k
  · have le : ∀ i, p₁' ⁻¹ᵁ ⊤ ⊓ (j ≫ p₂) ⁻¹ᵁ L.U i ≤ j ⁻¹ᵁ (p₁ ⁻¹ᵁ W ⊓ p₂ ⁻¹ᵁ L.U i) :=
      fun i z hz => ⟨hW z, hz.2⟩
    have key : ∀ (z : Y') (i : L.ι), p₂ (j z) ∈ L.U i →
        gs (𝟙 Y') z _ ((j.appLE _ _ (le i)).hom (σ i)) = (j.stalkMap z).hom (gs (𝟙 Y) (j z) _ (σ i)) := by
      intro z i hz
      rw [affine_gs_appLE j _ _ (le i) (𝟙 Y') z ⟨trivial, hz⟩, Category.id_comp,
        ← gs_comp j (𝟙 Y) z (p₁ ⁻¹ᵁ W ⊓ p₂ ⁻¹ᵁ L.U i) ⟨hW z, hz⟩, Category.comp_id]
    obtain ⟨c', hc'⟩ := h₂ (fun i => (j.appLE _ _ (le i)).hom (σ i)) (fun z i i' _ hi hi' => by
      rw [key z i hi, key z i' hi', hσ (j z) i i' (hW z) hi hi', map_mul]
      congr 1
      have : gm (j ≫ p₂) z (L.U i ⊓ L.U i') (L.g i i') =
          Units.map (j.stalkMap z).hom.toMonoidHom (gm p₂ (j z) (L.U i ⊓ L.U i') (L.g i i')) := by
        apply Units.ext
        rw [← gs_unit (j ≫ p₂) z (L.U i ⊓ L.U i') ⟨hi, hi'⟩, gs_comp j p₂ z (L.U i ⊓ L.U i') ⟨hi, hi'⟩,
          gs_unit p₂ (j z) (L.U i ⊓ L.U i') ⟨hi, hi'⟩]
        rfl
      rw [this, ← map_zpow (Units.map (j.stalkMap z).hom.toMonoidHom)]
      rfl)
    choose c hc using fun k => hb.2 (c' k)
    refine ⟨c, fun y i hy hi => ?_⟩
    obtain ⟨s, hs⟩ : p₁ y ∈ Set.range g := by rw [hr]; exact hy
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback sq y s hs.symm
    apply (ConcreteCategory.bijective_of_isIso (j.stalkMap z)).1
    have := hc' z i trivial hi
    rw [key z i hi, ← funext hc, affine_comb b p₁ p₂ W j p₁' g sq.w e c z i hi] at this
    exact this
end GlobalTheory.RelBasis
