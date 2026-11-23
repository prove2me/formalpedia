-- Prove2me | solution 1 for GlobalTheory.ZetaHalfPlane.measurable_fract_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:44.200236+00:00
-- url     : https://prove2.me/submissions/36ef1815-b4b2-430a-b910-07265649b125

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZetaEqSubIntegralFract
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtFractInt

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
theorem _root_.solution : Measurable fun t : ℝ => ((Int.fract t : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp measurable_fract
end GlobalTheory.ZetaHalfPlane
