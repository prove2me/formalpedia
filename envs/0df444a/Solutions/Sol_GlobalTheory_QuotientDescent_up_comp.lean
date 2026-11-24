-- Prove2me | solution 1 for GlobalTheory.QuotientDescent.up_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:19:09.608482+00:00
-- url     : https://prove2.me/submissions/fc37ddfb-e332-467a-8099-cacebc1286ca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsActionOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_QuotientDescendGrpObj
import Theorems.Thm_GlobalTheory_QuotientDescent_up_left
import Theorems.Thm_GlobalTheory_QuotientDescent_hom_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.QuotientDescent
variable {X X' : Scheme.{0}} {π : X ⟶ X'} {G : Over X} {G' : Over X'} {φ : G.left ⟶ G'.left}
namespace GlobalTheory.QuotientDescent
theorem _root_.solution (H : IsPullback φ G.hom G'.hom π) {T T' : Over X'} (u : T' ⟶ T) (z : T ⟶ G') :
    up H (u ≫ z) = (Over.pullback π).map u ≫ up H z := by
  refine hom_ext H ?_
  have A : ((Over.pullback π).map u).left ≫ pullback.fst T.hom π = pullback.fst T'.hom π ≫ u.left :=
    pullback.lift_fst _ _ _
  rw [up_left, Over.comp_left, Over.comp_left, Category.assoc, up_left, ← Category.assoc,
    ← Category.assoc, A]
end GlobalTheory.QuotientDescent
