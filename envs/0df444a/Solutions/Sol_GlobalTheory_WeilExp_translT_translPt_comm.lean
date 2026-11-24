-- Prove2me | solution 1 for GlobalTheory.WeilExp.translT_translPt_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:14:39.451207+00:00
-- url     : https://prove2.me/submissions/977ebbc9-608d-4195-9714-d18b41f0135f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_WeilIsExpRiemannForm

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
theorem _root_.solution [IsCommMonObj A] (x y : T ⟶ A) :
    (Out.translT A x).left ≫ (Out.translPt A y).left = (Out.translT A y).left ≫ (Out.translPt A x).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  show Out.translT A x ≫ ((fst T A ≫ y) * snd T A) = Out.translT A y ≫ ((fst T A ≫ x) * snd T A)
  rw [MonObj.comp_mul, MonObj.comp_mul, Out.translT, Out.translT, lift_snd, lift_snd, ← Category.assoc,
    ← Category.assoc, lift_fst, lift_fst]
  exact mul_left_comm _ _ _
end GlobalTheory.WeilExp
