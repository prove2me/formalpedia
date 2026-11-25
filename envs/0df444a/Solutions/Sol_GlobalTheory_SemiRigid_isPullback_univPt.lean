-- Prove2me | solution 1 for GlobalTheory.SemiRigid.isPullback_univPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:14:43.122413+00:00
-- url     : https://prove2.me/submissions/a467bbe7-bac8-4a98-935f-e0fb2e8759ae

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
import Theorems.Thm_GlobalTheory_LaurentConst_hom_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
variable {S : Scheme.{0}}
variable {R : CommRingCat.{0}} (X : Type) [AddCommGroup X] (t : Spec R ⟶ S)
namespace GlobalTheory.SemiRigid
theorem _root_.solution : IsPullback (univPt X t).left
    (Spec.map (CommRingCat.ofHom (algebraMap R (torusRing R X)))) (splitTorus S X).hom t := by
  refine IsPullback.of_right ?_ (Over.w _) (Diag.isPullback_torusFst S X)
  rw [show t ≫ toZ S = toZ _ from specULiftZIsTerminal.hom_ext _ _]
  have h := coord_ofCoord (T := grpSpec X t) (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom X
    ((Int.castRingHom R).comp (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ).toRingHom)) ≫
      (Scheme.ΓSpecIso (torusRing R X)).inv)
  have e : (univPt X t).left ≫ torusFst S X = _ :=
    ext_of_isAffine ((Iso.cancel_iso_inv_left (Scheme.ΓSpecIso _) _ _).1
      (h.trans (Scheme.ΓSpecIso_inv_naturality _)))
  rw [e]
  exact Diag.isPullback_groupRing R X
end GlobalTheory.SemiRigid
