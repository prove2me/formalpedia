-- Prove2me | solution 1 for GlobalTheory.SS.SectionTranslation.slice_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:12.974062+00:00
-- url     : https://prove2.me/submissions/6c3ec0b0-6ae4-45d2-bca7-9f439ad54306

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TranslationBySection

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
theorem _root_.solution {S : Scheme.{0}} (Y : Over S) (s : 𝟙_ (Over S) ⟶ Y) :
    IsPullback (lift (toUnit Y ≫ s) (𝟙 Y)).left Y.hom (fst Y Y).left s.left := by
  have hs : s.left ≫ Y.hom = 𝟙 S := Over.w s
  have h1 : (lift (toUnit Y ≫ s) (𝟙 Y)).left ≫ (snd Y Y).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]; rfl
  have h2 : (lift (toUnit Y ≫ s) (𝟙 Y)).left ≫ (fst Y Y).left = Y.hom ≫ s.left := by
    rw [← Over.comp_left, lift_fst]; rfl
  have h3 : IsPullback (snd Y Y).left (fst Y Y).left Y.hom Y.hom := (IsPullback.of_hasPullback Y.hom Y.hom).flip
  refine IsPullback.of_right ?_ h2 h3
  rw [h1, hs]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩
end GlobalTheory.SS.SectionTranslation
