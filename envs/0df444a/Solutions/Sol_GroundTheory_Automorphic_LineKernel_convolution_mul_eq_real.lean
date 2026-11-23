-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.convolution_mul_eq_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:42.966795+00:00
-- url     : https://prove2.me/submissions/bf5b80ad-edbf-4591-bdc0-31bb90f495d1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds

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
open scoped ContDiff Convolution Pointwise FourierTransform
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution (f g : ℝ → ℂ) : (f ⋆[mul ℂ ℂ] g) = (f ⋆[mul ℝ ℂ] g) := by
  funext x; simp only [convolution_def, mul_apply']
end GroundTheory.Automorphic.LineKernel
