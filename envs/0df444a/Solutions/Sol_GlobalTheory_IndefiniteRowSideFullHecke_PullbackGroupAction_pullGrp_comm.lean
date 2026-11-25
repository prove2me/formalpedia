-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.PullbackGroupAction.pullGrp_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:52:07.477918+00:00
-- url     : https://prove2.me/submissions/13ae31b8-cb74-4559-b679-ab5bab9c022d

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
theorem _root_.solution (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] : IsCommMonObj (pullGrp f G) :=
  inferInstance
end GlobalTheory.IndefiniteRowSideFullHecke.PullbackGroupAction
