-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SectionsGroupRank.neg_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:53:18.128579+00:00
-- url     : https://prove2.me/submissions/62ac68f3-d6e6-4df4-af60-0fb2d2c1092d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_SectionsGroupRank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SectionsGroupRank
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {S : Scheme.{0}} (A : Over S) [GrpObj A]
variable {A} {L : LB A.left} {a : ℤ} {T : Over S}
namespace GlobalTheory.IndefiniteRowSideFullHecke.SectionsGroupRank
theorem _root_.solution (s : Secs A L a T) (j) : LB.Sec.f (-s) j = - LB.Sec.f s j := rfl
end GlobalTheory.IndefiniteRowSideFullHecke.SectionsGroupRank
