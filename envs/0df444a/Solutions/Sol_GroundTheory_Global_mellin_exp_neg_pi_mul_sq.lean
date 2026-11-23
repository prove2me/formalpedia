-- Prove2me | solution 1 for GroundTheory.Global.mellin_exp_neg_pi_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:57.739462+00:00
-- url     : https://prove2.me/submissions/4940adf0-dee9-49f9-8c40-08b16004a45e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Gaussian
import Theorems.Thm_GroundTheory_Global_mellin_exp_neg_mul_sq

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
theorem _root_.solution {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t : ℝ ↦ ((Real.exp (-(π * t ^ 2)) : ℝ) : ℂ)) s = Gammaℝ s / 2 := by
  rw [mellin_exp_neg_mul_sq Real.pi_pos hs, Gammaℝ_def]
  ring_nf
end GroundTheory.Global
