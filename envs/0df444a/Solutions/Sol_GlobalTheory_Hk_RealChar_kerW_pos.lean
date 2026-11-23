-- Prove2me | solution 1 for GlobalTheory.Hk.RealChar.kerW_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:45.39322+00:00
-- url     : https://prove2.me/submissions/7d41d2ff-9b5c-44eb-8d1d-546ca26cc950

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormRayClassFamilyFOneGeOfRealCharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RealChar
namespace GlobalTheory.Hk.RealChar
theorem _root_.solution (y : ℝ) {w : ℝ} (hw : 0 < w) : 0 < kerW y w := by
  unfold kerW; positivity
end GlobalTheory.Hk.RealChar
