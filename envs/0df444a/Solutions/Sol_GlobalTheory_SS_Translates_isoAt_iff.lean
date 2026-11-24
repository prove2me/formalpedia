-- Prove2me | solution 1 for GlobalTheory.SS.Translates.isoAt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:42:51.5768+00:00
-- url     : https://prove2.me/submissions/d332aa8d-4c5a-4748-abd1-c7482aba70c5

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
import Theorems.Thm_GlobalTheory_SS_Translates_extends_iff

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
namespace GlobalTheory.SS.Translates
theorem _root_.solution {M : Model R A} {N : Model R A'} {f : A ⟶ A'} {y : M.Y.left} :
    IsoAt M N f y ↔ ∃ (X : Scheme.{0}) (i : X ⟶ M.Y.left) (g : X ⟶ N.Y.left) (o : X),
      IsOpenImmersion i ∧ IsOpenImmersion g ∧ Ext M N f i g ∧ i o = y := by
  constructor
  · rintro ⟨U, g, hy, he, hg⟩
    exact ⟨U, U.ι, g, ⟨y, hy⟩, inferInstance, hg, extends_iff.1 he, rfl⟩
  · rintro ⟨X, i, g, o, hi, hg, he, rfl⟩
    refine ⟨i.opensRange, i.isoOpensRange.inv ≫ g, ⟨o, rfl⟩, extends_iff.2 ⟨?_, fun T t a e => ?_⟩, inferInstance⟩
    · rw [Category.assoc, he.1, Scheme.Hom.isoOpensRange_inv_comp_assoc]
    · rw [← Category.assoc]
      exact he.2 _ _ _ (by rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, e])
end GlobalTheory.SS.Translates
