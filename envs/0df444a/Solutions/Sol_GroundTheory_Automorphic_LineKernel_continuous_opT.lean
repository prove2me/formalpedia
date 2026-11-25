-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.continuous_opT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:55:25.516482+00:00
-- url     : https://prove2.me/submissions/860d8503-fed6-4f17-9523-ec0e48fc3628

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution (a : ℕ → ℝ) (n : ℕ) {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) :
    Continuous (opT a n F) :=
  continuous_finsetSum _ fun p _ => continuous_const.mul
    (hF.continuous_iteratedDeriv p (by exact_mod_cast le_top))
end GroundTheory.Automorphic.LineKernel
