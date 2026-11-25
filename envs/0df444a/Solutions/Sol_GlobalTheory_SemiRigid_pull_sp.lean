-- Prove2me | solution 1 for GlobalTheory.SemiRigid.pull_sp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:28:47.956958+00:00
-- url     : https://prove2.me/submissions/1cb09812-037e-4cfd-b356-9204419d60fa

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_appTop_comp_apply


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
namespace GlobalTheory.SemiRigid
theorem _root_.solution {A C : CommRingCat.{0}} (ψ : A ⟶ C) {s : Spec A ⟶ S} {s' : Spec C ⟶ S}
    (h : Spec.map ψ ≫ s = s') {Y : Type} [AddCommGroup Y] (g : Over.mk s ⟶ splitTorus S Y)
    (u : Γ((splitTorus S Y).left, ⊤)) : pull (sp ψ h ≫ g) u = ψ.hom (pull g u) := by
  let p : Spec A ⟶ (splitTorus S Y).left := g.left
  change (Scheme.ΓSpecIso C).hom.hom ((Spec.map ψ ≫ p).appTop.hom u) =
    ψ.hom ((Scheme.ΓSpecIso A).hom.hom (p.appTop.hom u))
  rw [appTop_comp_apply, ← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality]
  rfl
end GlobalTheory.SemiRigid
