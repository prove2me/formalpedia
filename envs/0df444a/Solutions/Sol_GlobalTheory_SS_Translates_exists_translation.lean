-- Prove2me | solution 1 for GlobalTheory.SS.Translates.exists_translation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:05:54.445881+00:00
-- url     : https://prove2.me/submissions/f6bc6970-cc1e-4b4f-a565-5c93e20ed3b8

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
import Theorems.Thm_GlobalTheory_SS_Translates_isoAt_iff
import Theorems.Thm_GlobalTheory_SS_Translates_Ext_mem_sp
import Theorems.Thm_GlobalTheory_SS_Translates_exists_meet
import Theorems.Thm_GlobalTheory_SS_Translates_exists_section_open
import Theorems.Thm_GlobalTheory_SS_Translates_j_lift
import Theorems.Thm_GlobalTheory_SS_Translates_j_const
import Theorems.Thm_GlobalTheory_SS_Translates_slice_val
import Theorems.Thm_GlobalTheory_SS_Translates_slice_swap
import Theorems.Thm_GlobalTheory_SS_Translates_left_shear
import Theorems.Thm_GlobalTheory_SS_Translates_right_shear
import Theorems.Thm_GlobalTheory_SS_Translates_exists_shear_at
import Theorems.Thm_GlobalTheory_SS_SectionTranslation_translation_by_section


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
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' : Over (Sp K)}
variable [GrpObj A] [IsCommMonObj A]
namespace GlobalTheory.SS.Translates
theorem _root_.solution [IsDomain R] [IsLocalRing R] (hR : SH R K) (hA : IsAbelianScheme A) {M : Model R A}
    (hM : Strict M) (s s' : 𝟙_ (Over (Sp R)) ⟶ M.Y) {W : Scheme.{0}} (k : W ⟶ M.Y.left) [IsOpenImmersion k]
    {q : W} (hq : k q ∈ M.sp) :
    ∃ (c : 𝟙_ (Over (Sp K)) ⟶ A) (X : Scheme.{0}) (i g : X ⟶ M.Y.left) (o : X) (q' : W),
      IsOpenImmersion i ∧ IsOpenImmersion g ∧ Ext M M (transl c).hom i g ∧
      i o = s.left (IsLocalRing.closedPoint R) ∧ g o = k q' ∧
      IsoAt M M (transl c).hom (s'.left (IsLocalRing.closedPoint R)) := by
  have := hR.2.2.2
  have hirr : M.Irr := hM.1.1
  obtain ⟨a, ha, ⟨y, hy, hy'⟩, -⟩ := GlobalTheory.SS.SectionTranslation.translation_by_section R K hR A hA M hM s
  obtain ⟨X₀, i₀, g₀, o₀, hi₀, hg₀, e₀, rfl⟩ := isoAt_iff.1 hy'
  obtain ⟨p, p', hp, hp'⟩ := exists_meet hirr g₀ k ((e₀.mem_sp _).1 hy) hq
  obtain ⟨X₁, I₁, G₁, o₁, w₁, hI₁, hG₁, e₁, hw₁, ho₁⟩ := exists_shear_at hM s
  obtain ⟨X₂, I₂, G₂, o₂, w₂, hI₂, hG₂, e₂, hw₂, ho₂⟩ := exists_shear_at hM s'
  let U₀ : Set M.Y.left := i₀ '' (g₀ ⁻¹' Set.range k)
  let U₁ : Set M.Y.left := (lift (𝟙 M.Y) (toUnit M.Y ≫ s)).left ⁻¹' Set.range I₁
  let U₂ : Set M.Y.left := (lift (𝟙 M.Y) (toUnit M.Y ≫ s')).left ⁻¹' Set.range I₂
  have hU₀ : IsOpen U₀ := i₀.isOpenEmbedding.isOpenMap _ (k.isOpenEmbedding.isOpen_range.preimage g₀.continuous)
  have hU₁ : IsOpen U₁ := I₁.isOpenEmbedding.isOpen_range.preimage (Scheme.Hom.continuous _)
  have hU₂ : IsOpen U₂ := I₂.isOpenEmbedding.isOpen_range.preimage (Scheme.Hom.continuous _)
  have hne : (M.sp ∩ (U₀ ∩ (U₁ ∩ U₂))).Nonempty :=
    hirr.isPreirreducible _ _ hU₀ (hU₁.inter hU₂) ⟨i₀ p, (e₀.mem_sp _).2 hp, p, ⟨p', hp'.symm⟩, rfl⟩
      (hirr.isPreirreducible _ _ hU₁ hU₂ ⟨w₁, hw₁, o₁, ho₁⟩ ⟨w₂, hw₂, o₂, ho₂⟩)
  obtain ⟨t, ⟨r, ⟨q', hq'⟩, hr⟩, ⟨n₁, hn₁⟩, n₂, hn₂⟩ := exists_section_open hR M (hU₀.inter (hU₁.inter hU₂)) hne
  obtain ⟨c, hc, -, hc'⟩ := GlobalTheory.SS.SectionTranslation.translation_by_section R K hR A hA M hM t
  have m₁ := hn₁.trans (slice_swap M t s _)
  have m₂ := hn₂.trans (slice_swap M t s' _)
  have k₁ : IsoAt M M (transl c).hom (s.left (IsLocalRing.closedPoint R)) :=
    hc' _ true (isoAt_iff.2 ⟨X₁, I₁, G₁, n₁, hI₁, hG₁, e₁, m₁⟩)
  have k₂ : IsoAt M M (transl c).hom (s'.left (IsLocalRing.closedPoint R)) :=
    hc' _ true (isoAt_iff.2 ⟨X₂, I₂, G₂, n₂, hI₂, hG₂, e₂, m₂⟩)
  obtain ⟨X, i, g, o, hi, hg, e, ho⟩ := isoAt_iff.1 k₁
  refine ⟨c, X, i, g, o, q', hi, hg, e, ho, ?_, k₂⟩
  have v₁ := slice_val M _ _ (j_lift M _ (𝟙 _) _ (𝟙 _) (j_const M t c hc) (by simp)) _ (left_shear c) e e₁
    (m₁.trans (congrArg _ ho.symm))
  have v₂ := slice_val M _ _ (j_lift M (𝟙 _) _ (𝟙 _) _ (by simp) (j_const M s a ha)) _ (right_shear a) e₀ e₁
    (hn₁.trans (congrArg _ hr.symm))
  exact v₁.trans (v₂.symm.trans hq'.symm)
end GlobalTheory.SS.Translates
