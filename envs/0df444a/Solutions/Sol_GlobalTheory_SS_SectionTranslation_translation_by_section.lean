-- Prove2me | solution 1 for GlobalTheory.SS.SectionTranslation.translation_by_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:56:08.262717+00:00
-- url     : https://prove2.me/submissions/5e297624-0e4b-40d3-b0b4-bcbe44d69bbe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TranslationBySection
import Theorems.Thm_GlobalTheory_SS_SectionTranslation_j_isPullback
import Theorems.Thm_GlobalTheory_SS_SectionTranslation_slice_isPullback
import Theorems.Thm_GlobalTheory_SS_SectionTranslation_isoAt_slice
import Theorems.Thm_GlobalTheory_SS_SectionTranslation_slice_shear
import Theorems.Thm_GlobalTheory_SS_SectionTranslation_shear_fst

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
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, Strict M → ∀ (s : 𝟙_ (Over (Sp R)) ⟶ M.Y), ∃ a : (𝟙_ (Over (Sp K)) ⟶ A), a.left ≫ M.j = spMap (algebraMap R K) ≫ s.left ∧ GenIso M M (transl a).hom ∧ ∀ (y : M.Y.left) (b : Bool), IsoAt (M.prod M) (M.prod M) (shear A b) ((lift (toUnit M.Y ≫ s) (𝟙 M.Y)).left y) → IsoAt M M (if b then (transl a).hom else (transl a).inv) y := by
  intro R K _ _ _ _ _ hSH A _ _ _ M hM s
  have := hSH.2.2.2
  have hs : s.left ≫ M.Y.hom = 𝟙 (Sp R) := Over.w s
  have w : (spMap (algebraMap R K) ≫ s.left) ≫ M.Y.hom = 𝟙 (Sp K) ≫ spMap (algebraMap R K) := by
    rw [Category.assoc, hs]; simp
  let a : 𝟙_ (Over (Sp K)) ⟶ A := Over.homMk ((j_isPullback M).lift _ _ w) ((j_isPullback M).lift_snd _ _ w)
  have ha : a.left ≫ M.j = spMap (algebraMap R K) ≫ s.left := (j_isPullback M).lift_fst _ _ w
  have key : ∀ (y : M.Y.left) (b : Bool), IsoAt (M.prod M) (M.prod M) (shear A b)
      ((lift (toUnit M.Y ≫ s) (𝟙 M.Y)).left y) → IsoAt M M (if b then (transl a).hom else (transl a).inv) y := by
    intro y b h
    rw [← slice_shear]
    exact isoAt_slice M s a ha _ (shear_fst b) y h
  refine ⟨a, ha, ?_, key⟩
  have hx : s.left (IsLocalRing.closedPoint R) ∈ M.sp :=
    congrArg (fun q : Sp R ⟶ Sp R => q (IsLocalRing.closedPoint R)) hs
  obtain ⟨z, hz, hi⟩ := (hM.2 true _ hx).1
  obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback (slice_isPullback M.Y s) z _ hz
  exact ⟨y, hy, key y true hi⟩
end GlobalTheory.SS.SectionTranslation
