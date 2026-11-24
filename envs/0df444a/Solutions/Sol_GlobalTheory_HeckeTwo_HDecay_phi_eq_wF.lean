-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.HDecay.phi_eq_wF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:21:54.064001+00:00
-- url     : https://prove2.me/submissions/78686a6a-9473-43e6-ad77-5faa7c865f9c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformRapidDecay
import Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_add_I_ne

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
variable {σ y}
namespace GlobalTheory.HeckeTwo.HDecay
theorem _root_.solution (hy : y ≠ 0) (t : ℝ) : phi σ ((t : ℂ) + (y : ℂ) * I) = wF σ y 0 0 t := by
  have hz := add_I_ne hy t
  have hn : 0 < ‖(t : ℂ) + (y : ℂ) * I‖ := norm_pos_iff.2 hz
  simp only [phi, wF, gI, eF, pow_zero, mul_one, zero_add]
  congr 1
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne'), ← Complex.ofReal_log hn.le]
  congr 1
  have e : t ^ 2 + y ^ 2 = ‖(t : ℂ) + (y : ℂ) * I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  rw [e, Real.log_pow]
  push_cast
  ring
end GlobalTheory.HeckeTwo.HDecay
