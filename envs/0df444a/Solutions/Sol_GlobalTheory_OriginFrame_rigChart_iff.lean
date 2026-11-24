-- Prove2me | solution 1 for GlobalTheory.OriginFrame.rigChart_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:19:34.540854+00:00
-- url     : https://prove2.me/submissions/2900764b-b79e-463f-b640-c33fbfc26dd6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsAppellHumbertFrameIsRig

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
open GlobalTheory
open GlobalTheory.OriginFrame
namespace GlobalTheory.OriginFrame
theorem _root_.solution {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (L : LB X) (j : (L.pull x).ι) :
    ⊤ ≤ (L.pull x).U j ↔ ⊤ ≤ x ⁻¹ᵁ L.U (j PUnit.unit) := by
  delta LB.pull LB.LinComb LB.wchart
  constructor
  · intro h p _
    exact Set.mem_iInter.mp (h trivial) PUnit.unit
  · intro h p hp
    exact Set.mem_iInter.mpr (fun k => by cases k; exact h hp)
end GlobalTheory.OriginFrame
