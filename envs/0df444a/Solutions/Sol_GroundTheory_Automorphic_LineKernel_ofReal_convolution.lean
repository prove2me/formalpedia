-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.ofReal_convolution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:55:19.696808+00:00
-- url     : https://prove2.me/submissions/395c1d7d-ece6-442d-8b3c-d21455b869f0

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
theorem _root_.solution (f g : ℝ → ℝ) (x : ℝ) :
    (((f ⋆[mul ℝ ℝ] g) x : ℝ) : ℂ) =
      ((fun t => (f t : ℂ)) ⋆[mul ℂ ℂ] (fun t => (g t : ℂ))) x := by
  rw [convolution_mul, convolution_mul, ← integral_complex_ofReal]
  push_cast; rfl
end GroundTheory.Automorphic.LineKernel
