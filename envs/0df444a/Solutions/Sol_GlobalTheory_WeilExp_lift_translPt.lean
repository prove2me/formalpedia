-- Prove2me | solution 1 for GlobalTheory.WeilExp.lift_translPt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:03:00.359119+00:00
-- url     : https://prove2.me/submissions/35686714-f52a-429d-84f3-5c635cc589fa

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
theorem _root_.solution {W : Over S} (p : W ⟶ T) (q : W ⟶ A) (x : T ⟶ A) :
    lift p q ≫ Out.translPt A x = (p ≫ x) * q := by
  show lift p q ≫ ((fst T A ≫ x) * snd T A) = _
  rw [MonObj.comp_mul, lift_snd, ← Category.assoc, lift_fst]
end GlobalTheory.WeilExp
