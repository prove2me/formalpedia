-- Prove2me | solution 1 for GlobalTheory.SemiRigid.torus_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:37:49.072346+00:00
-- url     : https://prove2.me/submissions/fd343521-5a1c-4bde-ae98-cb7c37252dab

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_OneTmulNeZeroOfDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsNoetherianModelOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqCompSectionOfSurjectiveAppTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SurjectiveAppOfIsAbelianScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GroupRingHomConstOfLaurent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsTorusAndQuotientHom
import Theorems.Thm_GlobalTheory_groupRing_hom_const_of_laurent
import Theorems.Thm_GlobalTheory_laurent_point_const


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SemiRigid
open SplitTorus
variable {K : Type} [Field K]
namespace GlobalTheory.SemiRigid
theorem _root_.solution (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (B : Over (Spec (.of K))) [GrpObj B] [IsProper B.hom] (f : splitTorus (Spec (.of K)) X ⟶ B) :
    f = toUnit _ ≫ η ≫ f := by
  obtain ⟨k, e⟩ := groupRing_hom_const_of_laurent B.hom (laurent_point_const B) K X (𝟙 _)
    ((torusIso K X).hom ≫ f.left) (by rw [Category.assoc, Over.w, torusIso_hom_hom, Category.comp_id])
  rw [← torusIso_hom_hom, Category.assoc, cancel_epi] at e
  have hη : (η : 𝟙_ _ ⟶ splitTorus (Spec (.of K)) X).left ≫ (splitTorus (Spec (.of K)) X).hom =
    𝟙 _ := Over.w _
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, e, reassoc_of% hη]
  rfl
end GlobalTheory.SemiRigid
