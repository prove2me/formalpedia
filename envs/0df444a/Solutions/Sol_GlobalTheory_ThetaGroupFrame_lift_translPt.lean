-- Prove2me | solution 1 for GlobalTheory.ThetaGroupFrame.lift_translPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:31:13.541271+00:00
-- url     : https://prove2.me/submissions/d14ac226-f4c1-46e8-b772-1cade6a1fd65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaGroupFrame
namespace GlobalTheory.ThetaGroupFrame
theorem _root_.solution {S : Scheme.{0}} (A : Over S) [GrpObj A] {T B : Over S} (p : B ⟶ T)
    (x : T ⟶ A) (y : B ⟶ A) : lift p y ≫ Out.translPt A x = (p ≫ x) * y := by
  unfold Out.translPt
  rw [CategoryTheory.Hom.mul_def, ← Category.assoc, CartesianMonoidalCategory.comp_lift]
  simp
end GlobalTheory.ThetaGroupFrame
