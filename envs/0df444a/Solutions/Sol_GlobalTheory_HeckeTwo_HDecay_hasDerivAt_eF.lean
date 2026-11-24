-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.HDecay.hasDerivAt_eF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:45:45.222435+00:00
-- url     : https://prove2.me/submissions/92af573d-23f4-4a57-9bb2-f5d9318f1650

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformRapidDecay
import Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_sq_add_sq_pos
import Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_gI_add_hI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex MeasureTheory
open scoped ContDiff FourierTransform
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.HDecay
variable (σ : ℂ) (y : ℝ)
variable {y}
namespace GlobalTheory.HeckeTwo.HDecay
theorem _root_.solution (hy : y ≠ 0) (t : ℝ) :
    HasDerivAt (eF σ y) (-σ * (gI y t + hI y t) * eF σ y t) t := by
  have hpos := sq_add_sq_pos hy t
  have hL : HasDerivAt (fun s : ℝ => Real.log (s ^ 2 + y ^ 2)) (2 * t / (t ^ 2 + y ^ 2)) t := by
    have := ((hasDerivAt_pow 2 t).add_const (y ^ 2)).log hpos.ne'
    convert this using 1
    ring
  have hc := ((hL.ofReal_comp).const_mul (-σ)).cexp
  refine hc.congr_deriv ?_
  rw [gI_add_hI hy t]
  simp only [eF]
  ring
end GlobalTheory.HeckeTwo.HDecay
