-- Prove2me | solution 1 for GroundTheory.Global.hasDerivAt_realGaussian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:09:55.920243+00:00
-- url     : https://prove2.me/submissions/79fc5e4d-d115-4c0b-9dea-488b88a36039

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Gaussian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Complex MeasureTheory Set Real
open scoped FourierTransform
noncomputable section
namespace GroundTheory.Global
theorem _root_.solution (x : ℝ) :
    HasDerivAt realGaussian (-2 * π * x * realGaussian x) x := by
  have h : HasDerivAt (fun y : ℝ ↦ -π * (y : ℂ) ^ 2) (-π * (2 * (x : ℂ))) x := by
    have := ((hasDerivAt_id x).ofReal_comp).pow 2
    simpa using this.const_mul (-(π : ℂ))
  unfold realGaussian
  convert h.cexp using 1
  ring
end GroundTheory.Global
