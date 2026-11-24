-- Prove2me | solution 1 for GlobalTheory.SS.SectionTranslation.isoAt_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:41:09.446855+00:00
-- url     : https://prove2.me/submissions/bc84999b-8114-43d9-9230-c776f626cfb5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TranslationBySection
import Theorems.Thm_GlobalTheory_SS_SectionTranslation_prod_j_fst
import Theorems.Thm_GlobalTheory_SS_SectionTranslation_prod_j_snd
import Theorems.Thm_GlobalTheory_SS_SectionTranslation_extends_apply
import Theorems.Thm_GlobalTheory_SS_SectionTranslation_ext_generic
import Theorems.Thm_GlobalTheory_SS_SectionTranslation_slice_isPullback
import Theorems.Thm_GlobalTheory_SS_Model_j_hom


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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.SectionTranslation
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}
namespace GlobalTheory.SS.SectionTranslation
theorem _root_.solution [IsDomain R] [IsFractionRing R K] (M : Model R A) (s : 𝟙_ (Over (Sp R)) ⟶ M.Y)
    (a : 𝟙_ (Over (Sp K)) ⟶ A) (ha : a.left ≫ M.j = spMap (algebraMap R K) ≫ s.left)
    (f : A ⊗ A ⟶ A ⊗ A) (hf : f ≫ fst A A = fst A A) (y : M.Y.left)
    (h : IsoAt (M.prod M) (M.prod M) f ((lift (toUnit M.Y ≫ s) (𝟙 M.Y)).left y)) :
    IsoAt M M (lift (toUnit A ≫ a) (𝟙 A) ≫ f ≫ snd A A) y := by
  obtain ⟨U, g, hy, he, hg⟩ := h
  have hsl := slice_isPullback M.Y s
  have h1 : (lift (toUnit M.Y ≫ s) (𝟙 M.Y)).left ≫ (snd M.Y M.Y).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]; rfl
  obtain ⟨i, hi⟩ : ∃ i : M.Y.left ⟶ (M.prod M).Y.left, i = (lift (toUnit M.Y ≫ s) (𝟙 M.Y)).left := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : (M.prod M).Y.left ⟶ M.Y.left, p = (fst M.Y M.Y).left := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ p : (M.prod M).Y.left ⟶ M.Y.left, p = (snd M.Y M.Y).left := ⟨_, rfl⟩
  let a' : Sp K ⟶ A.left := a.left
  let s' : Sp R ⟶ M.Y.left := s.left
  replace ha : a' ≫ M.j = spMap (algebraMap R K) ≫ s' := ha
  have hy : i y ∈ U := hi ▸ hy
  replace hsl : IsPullback i M.Y.hom p s' := by subst hi hp; exact hsl
  replace h1 : i ≫ q = 𝟙 _ := by subst hi hq; exact h1
  have hjp : (M.prod M).j ≫ p = (fst A A).left ≫ M.j := by subst hp; exact prod_j_fst M M
  have hjq : (M.prod M).j ≫ q = (snd A A).left ≫ M.j := by subst hq; exact prod_j_snd M M
  have h3 : IsPullback p q M.Y.hom M.Y.hom := by subst hp hq; exact IsPullback.of_hasPullback _ _
  have hph : p ≫ M.Y.hom = (M.prod M).Y.hom := by subst hp; rfl
  have hqh : q ≫ M.Y.hom = (M.prod M).Y.hom := by rw [← h3.w, hph]
  have hih : i ≫ (M.prod M).Y.hom = M.Y.hom := by rw [← hqh, ← Category.assoc, h1, Category.id_comp]
  clear hi hp hq
  have hj : (lift (toUnit A ≫ a) (𝟙 A)).left ≫ (M.prod M).j = M.j ≫ i := by
    refine h3.hom_ext ?_ ?_
    · have e1 : (lift (toUnit A ≫ a) (𝟙 A)).left ≫ (fst A A).left = A.hom ≫ a' := (slice_isPullback A a).w
      rw [Category.assoc, Category.assoc, hsl.w, ← Category.assoc M.j, M.j_hom, Category.assoc, ← ha, hjp,
        ← Category.assoc, e1, Category.assoc]
    · have e1 : (lift (toUnit A ≫ a) (𝟙 A)).left ≫ (snd A A).left = 𝟙 _ := by
        rw [← Over.comp_left, lift_snd]; rfl
      rw [Category.assoc, Category.assoc, h1, hjq, ← Category.assoc, e1]; simp
  have := M.sep
  have hgp : g ≫ p = U.ι ≫ p := by
    refine ext_generic (M.prod M) U M.Y.hom ?_ ?_
    · rw [Category.assoc, Category.assoc, hph, he.1]
    · rw [← Category.assoc, he.2, ← Category.assoc (_ ∣_ _), morphismRestrict_ι, Category.assoc, Category.assoc,
        Category.assoc, hjp, ← Category.assoc f.left, ← Over.comp_left, hf]
  have hV := isPullback_morphismRestrict i U
  have hg1 : ((i ∣_ U) ≫ g ≫ q) ≫ M.Y.hom = (i ⁻¹ᵁ U).ι ≫ M.Y.hom := by
    rw [Category.assoc, Category.assoc, hqh, he.1, ← Category.assoc, morphismRestrict_ι, Category.assoc, hih]
  have hg2 : ((i ∣_ U) ≫ g ≫ q) ≫ i = (i ∣_ U) ≫ g := by
    refine h3.hom_ext ?_ ?_
    · rw [Category.assoc _ i, hsl.w, ← Category.assoc, hg1, Category.assoc, Category.assoc, hgp, ← hsl.w,
        ← Category.assoc, ← Category.assoc, morphismRestrict_ι]
    · rw [Category.assoc _ i, h1]; simp
  have hpb : IsPullback ((i ∣_ U) ≫ g ≫ q) (i ∣_ U) i g := by
    refine IsPullback.of_right ?_ hg2 hsl.flip
    rw [hg1, hgp]
    exact hV.flip.paste_horiz hsl.flip
  refine ⟨i ⁻¹ᵁ U, (i ∣_ U) ≫ g ≫ q, hy, ⟨hg1, ?_⟩, MorphismProperty.of_isPullback hpb.flip hg⟩
  have e := extends_apply he ((M.j ⁻¹ᵁ (i ⁻¹ᵁ U)).ι ≫ (lift (toUnit A ≫ a) (𝟙 A)).left)
    ((M.j ∣_ (i ⁻¹ᵁ U)) ≫ (i ∣_ U)) (by
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, morphismRestrict_ι, Category.assoc, Category.assoc, hj])
  rw [← Category.assoc, ← Category.assoc, e]
  simp only [Category.assoc, hjq, Over.comp_left]
end GlobalTheory.SS.SectionTranslation
