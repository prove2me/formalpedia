-- Prove2me | solution 1 for GlobalTheory.ZetaHalfPlane.norm_cutFract_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:20:20.208386+00:00
-- url     : https://prove2.me/submissions/8e3a2099-b00f-47e3-b189-55c5979e3b5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZetaEqSubIntegralFract
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtFractInt
import Theorems.Thm_GlobalTheory_ZetaHalfPlane_norm_fract_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Set Filter Topology
open GlobalTheory GlobalTheory.ZetaHalfPlane
namespace GlobalTheory.ZetaHalfPlane
theorem _root_.solution (t : ℝ) : ‖cutFract t‖ ≤ 1 :=
  (norm_indicator_le_norm_self _ _).trans (norm_fract_le t)
end GlobalTheory.ZetaHalfPlane
