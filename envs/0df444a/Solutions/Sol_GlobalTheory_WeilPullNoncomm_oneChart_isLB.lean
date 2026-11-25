-- Prove2me | solution 1 for GlobalTheory.WeilPullNoncomm.oneChart_isLB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:28:47.722721+00:00
-- url     : https://prove2.me/submissions/64bb6883-4847-45da-b9af-3ddc9c76757e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotWeilIsGrpPullback

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeilPullNoncomm
open GlobalTheory.CommPairing
namespace GlobalTheory.WeilPullNoncomm
theorem _root_.solution (X : Scheme.{0}) : (oneChart X).IsLB where
  cover := top_le_iff.1 fun _ _ => TopologicalSpace.Opens.mem_iSup.2 ⟨PUnit.unit, trivial⟩
  g_self _ := map_one _
  cocycle _ _ _ := by
    show res _ 1 * res _ 1 = res _ 1
    simp only [map_one, _root_.mul_one]
end GlobalTheory.WeilPullNoncomm
