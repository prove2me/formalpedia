-- Prove2me | solution 1 for GroundTheory.Global.fourier_realGaussian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:46.207315+00:00
-- url     : https://prove2.me/submissions/0ab997df-7b91-40e8-a165-b18b71cc10d2

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
theorem _root_.solution : 𝓕 realGaussian = realGaussian := by
  have h := fourier_gaussian_pi (b := 1) (by simp)
  simp only [mul_one, one_cpow, div_one, one_mul] at h
  unfold realGaussian
  rw [h]
end GroundTheory.Global
