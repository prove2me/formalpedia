-- Prove2me | solution 1 for GlobalTheory.ZetaHalfPlane.measurable_cutFract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:20:19.331255+00:00
-- url     : https://prove2.me/submissions/6cc400ba-4c23-4836-911a-6490ec19cdd5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZetaEqSubIntegralFract
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtFractInt
import Theorems.Thm_GlobalTheory_ZetaHalfPlane_measurable_fract_ofReal

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
theorem _root_.solution : Measurable cutFract :=
  measurable_fract_ofReal.indicator measurableSet_Ioi
end GlobalTheory.ZetaHalfPlane
