-- Prove2me | solution 1 for GlobalTheory.AbLaw.CubeOpen.isPullback_sqMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:54.400908+00:00
-- url     : https://prove2.me/submissions/9a28330b-8ea8-440b-9975-e645214a9eb3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivBasicOpenOfTrivFibre
import Theorems.Thm_GlobalTheory_AbLaw_CubeOpen_isPullback_iso_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeOpen
variable {S S' : Scheme.{0}} (φ : S' ⟶ S) (A : Over S)
namespace GlobalTheory.AbLaw.CubeOpen
theorem _root_.solution :
    IsPullback (sqMap φ A) ((Over.pullback φ).obj A ⊗ (Over.pullback φ).obj A).hom (A ⊗ A).hom φ := by
  have h := IsPullback.of_hasPullback (A ⊗ A).hom φ
  have hw := Over.w (Functor.LaxMonoidal.μ (Over.pullback φ) A A)
  haveI : IsIso (Functor.LaxMonoidal.μ (Over.pullback φ) A A).left :=
    (Over.forget S').map_isIso (Functor.LaxMonoidal.μ (Over.pullback φ) A A)
  rw [← hw]
  exact isPullback_iso_comp h _
end GlobalTheory.AbLaw.CubeOpen
