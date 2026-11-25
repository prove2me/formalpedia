-- Prove2me | solution 1 for GroundTheory.Global.ofReal_cpow_div_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:09:17.998048+00:00
-- url     : https://prove2.me/submissions/24faae2a-2d16-4b0c-88d1-5d003191d521

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
theorem _root_.solution {y : ℝ} (hy : 0 < y) (s : ℂ) :
    (y : ℂ) ^ s / (y : ℂ) = (y : ℂ) ^ (s - 1) := by
  have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  rw [cpow_sub _ _ hy', cpow_one]
end GroundTheory.Global
