-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SectionsGroupRank.isPullSec_pullSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:40:02.012008+00:00
-- url     : https://prove2.me/submissions/8a56557c-9370-49f4-947b-18ed2bdb1b32

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
theorem _root_.solution {T' : Over S} (u : T' ⟶ T) (s : Secs A L a T) :
    IsPullSec A L a (u ▷ A) (whiskerRight_snd _ _) s (pullSec u s) := fun _ => rfl
end GlobalTheory.IndefiniteRowSideFullHecke.SectionsGroupRank
