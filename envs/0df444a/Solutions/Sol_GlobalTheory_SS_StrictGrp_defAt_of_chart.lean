-- Prove2me | solution 1 for GlobalTheory.SS.StrictGrp.defAt_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:22:26.905629+00:00
-- url     : https://prove2.me/submissions/3c1727af-5129-422e-9db7-7b8e143f54e0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnionTranslatesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelExtensionOfDefinedAtPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TranslationBySection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyIntegralOfIsIntegralOfIsAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGrpObjOfStrictBirationalLaw

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.StrictGrp
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' : Over (Sp K)}
namespace GlobalTheory.SS.StrictGrp
theorem _root_.solution {G : Model R A} {N : Model R A'} {φ : A ⟶ A'} {W V : Scheme.{0}} (w : W ⟶ G.Y.left)
    [IsOpenImmersion w] {v : V ⟶ W} {u : V ⟶ A.left} (hp : IsPullback v u w G.j) (h : W ⟶ N.Y.left)
    (h₁ : h ≫ N.Y.hom = w ≫ G.Y.hom) (h₂ : v ≫ h = u ≫ φ.left ≫ N.j) {y : G.Y.left} (hy : y ∈ Set.range w) :
    DefAt G N φ y := by
  refine ⟨w.opensRange, w.isoOpensRange.inv ≫ h, hy, ?_, ?_⟩
  · rw [Category.assoc, h₁, ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
  · have e : (G.j ∣_ w.opensRange ≫ w.isoOpensRange.inv) ≫ w = (G.j ⁻¹ᵁ w.opensRange).ι ≫ G.j := by
      rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
    rw [← Category.assoc, ← hp.lift_fst _ _ e, Category.assoc, h₂, ← Category.assoc, hp.lift_snd]
end GlobalTheory.SS.StrictGrp
