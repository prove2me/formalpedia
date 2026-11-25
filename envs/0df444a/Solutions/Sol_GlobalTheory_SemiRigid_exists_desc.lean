-- Prove2me | solution 1 for GlobalTheory.SemiRigid.exists_desc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:44:42.233173+00:00
-- url     : https://prove2.me/submissions/dcee76c0-f729-4c39-b8df-b62b372bacec

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
theorem _root_.solution {G B Y : Over S} (p : G ⟶ B) [Flat p.left] [Surjective p.left]
    [QuasiCompact p.left] (f : G ⟶ Y)
    (H : ∀ (Z : Over S) (a b : Z ⟶ G), a ≫ p = b ≫ p → a ≫ f = b ≫ f) : ∃ g, p ≫ g = f := by
  have H' : ∀ {Z : Scheme.{0}} (a b : Z ⟶ G.left), a ≫ p.left = b ≫ p.left →
      a ≫ f.left = b ≫ f.left := fun {Z} a b h ↦
    congrArg (·.left) (H (Over.mk (a ≫ G.hom)) (Over.homMk a rfl) (Over.homMk b (by
      change b ≫ G.hom = a ≫ G.hom
      rw [← Over.w p, reassoc_of% h])) (Over.OverMorphism.ext h))
  have e := EffectiveEpi.fac p.left f.left H'
  refine ⟨Over.homMk (EffectiveEpi.desc p.left f.left H') ?_, Over.OverMorphism.ext e⟩
  rw [← cancel_epi p.left, reassoc_of% e, Over.w, Over.w]
end GlobalTheory.SemiRigid
