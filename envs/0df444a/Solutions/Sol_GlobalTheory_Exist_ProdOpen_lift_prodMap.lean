-- Prove2me | solution 1 for GlobalTheory.Exist.ProdOpen.lift_prodMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:44:58.525338+00:00
-- url     : https://prove2.me/submissions/9a535699-8e5e-44c4-b854-44be9f98a135

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKernelVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivBasicOpenOfTrivFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TrivProdOfSmallExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LineBundleTrivialBasicOpenOfTrivialFibreProduct

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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.AbLaw.CubeOpen
noncomputable section
open GlobalTheory GlobalTheory.Exist GlobalTheory.Exist.ProdOpen
variable {S S' : Scheme.{0}} (φ : S' ⟶ S) (X Y : Over S)
namespace GlobalTheory.Exist.ProdOpen
theorem _root_.solution {Z : Over S} (a : Z ⟶ X) (b : Z ⟶ Y) :
    (lift ((Over.pullback φ).map a) ((Over.pullback φ).map b)).left ≫ prodMap φ X Y =
      pullback.fst Z.hom φ ≫ (lift a b).left := by
  rw [prodMap, ← Category.assoc, ← Over.comp_left, Functor.Monoidal.lift_μ]
  exact pullback.lift_fst _ _ _
end GlobalTheory.Exist.ProdOpen
