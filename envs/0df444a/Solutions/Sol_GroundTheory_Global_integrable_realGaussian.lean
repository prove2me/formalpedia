-- Prove2me | solution 1 for GroundTheory.Global.integrable_realGaussian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:09:58.755741+00:00
-- url     : https://prove2.me/submissions/ec9341a9-231d-45b3-9f8d-d54fe105e99f

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
theorem _root_.solution : Integrable realGaussian := by
  exact integrable_cexp_neg_mul_sq (b := (π : ℂ)) (by simpa using Real.pi_pos)
end GroundTheory.Global
