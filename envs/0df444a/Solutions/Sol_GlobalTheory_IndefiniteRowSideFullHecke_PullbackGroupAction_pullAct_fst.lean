-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.PullbackGroupAction.pullAct_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:52:03.708184+00:00
-- url     : https://prove2.me/submissions/c53704ae-110a-4f63-9420-553a6f452522

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrData
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PullbackGroupAction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.PullbackGroupAction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {S S' : Scheme.{0}}
namespace GlobalTheory.IndefiniteRowSideFullHecke.PullbackGroupAction
theorem _root_.solution {O : Type} [CommRing O] (f : S' ⟶ S) {G : Over S} [GrpObj G] (A : OAct O G) (a : O) :
    ((pullAct f A).act a).left ≫ pullFst f G = pullFst f G ≫ (A.act a).left := by
  exact pullback.lift_fst _ _ _
end GlobalTheory.IndefiniteRowSideFullHecke.PullbackGroupAction
