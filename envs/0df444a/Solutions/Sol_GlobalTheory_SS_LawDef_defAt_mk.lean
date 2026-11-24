-- Prove2me | solution 1 for GlobalTheory.SS.LawDef.defAt_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:06:04.040056+00:00
-- url     : https://prove2.me/submissions/e447a9cd-5b87-4313-9860-7b4803fc9de7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TranslationBySection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelGroupLawDefinedAtTranslate

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
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.LawDef
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' : Over (Sp K)}
namespace GlobalTheory.SS.LawDef
theorem _root_.solution (M : Model R A) (N : Model R A') (f : A ⟶ A') {V : Scheme.{0}} (i : V ⟶ M.Y.left)
    [IsOpenImmersion i] (g : V ⟶ N.Y.left) (h1 : g ≫ N.Y.hom = i ≫ M.Y.hom)
    (h2 : ∀ (T : Scheme.{0}) (t : T ⟶ A.left) (u : T ⟶ V), u ≫ i = t ≫ M.j → u ≫ g = t ≫ f.left ≫ N.j) (y : V) :
    DefAt M N f (i y) := by
  refine ⟨i.opensRange, i.isoOpensRange.inv ≫ g, ⟨y, rfl⟩, ?_, ?_⟩
  · rw [Category.assoc, h1, Scheme.Hom.isoOpensRange_inv_comp_assoc]
  · rw [← Category.assoc]
    apply h2
    rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
end GlobalTheory.SS.LawDef
