-- Prove2me | solution 1 for GroundTheory.Global.integral_comp_abs_complex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:14.937697+00:00
-- url     : https://prove2.me/submissions/6794878c-9eff-4a86-bb2e-3bf17b64be5c

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
theorem _root_.solution (f : ℝ → ℂ) :
    ∫ x : ℝ, f |x| = 2 * ∫ y in Ioi (0 : ℝ), f y := by
  have h := integral_fun_norm_addHaar (volume : Measure ℝ) f
  simp only [Real.norm_eq_abs] at h
  rw [h]
  simp [Complex.real_smul]
end GroundTheory.Global
