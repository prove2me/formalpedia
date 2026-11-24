-- Prove2me | solution 1 for GlobalTheory.AbLaw.CubeOpen.lift_sqMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:53:05.078596+00:00
-- url     : https://prove2.me/submissions/2470ef28-6e08-4737-bf0f-8f0c5478f689

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivBasicOpenOfTrivFibre

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
theorem _root_.solution (a b : A ⟶ A) :
    (lift ((Over.pullback φ).map a) ((Over.pullback φ).map b)).left ≫ sqMap φ A =
      pullback.fst A.hom φ ≫ (lift a b).left := by
  rw [sqMap, ← Category.assoc, ← Over.comp_left, Functor.Monoidal.lift_μ]
  exact pullback.lift_fst _ _ _
end GlobalTheory.AbLaw.CubeOpen
