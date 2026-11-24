-- Prove2me | solution 1 for GlobalTheory.WeilExp.lift_translT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:14:37.376106+00:00
-- url     : https://prove2.me/submissions/062250c2-da0f-4742-b88e-9ccd05dc2432

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_WeilIsExpRiemannForm
import Theorems.Thm_GlobalTheory_WeilExp_lift_translPt

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
noncomputable section
open GlobalTheory GlobalTheory.WeilExp
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S}
namespace GlobalTheory.WeilExp
theorem _root_.solution {W : Over S} (p : W ⟶ T) (q : W ⟶ A) (x : T ⟶ A) :
    lift p q ≫ Out.translT A x = lift p ((p ≫ x) * q) := by
  rw [Out.translT, comp_lift, lift_fst, lift_translPt]
end GlobalTheory.WeilExp
