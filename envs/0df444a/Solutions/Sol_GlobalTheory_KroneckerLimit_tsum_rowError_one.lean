-- Prove2me | solution 1 for GlobalTheory.KroneckerLimit.tsum_rowError_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:43:48.068022+00:00
-- url     : https://prove2.me/submissions/688b1523-387f-4ed8-9f47-54bf8dbbef12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SummableAndAbsTsumSubIntegralLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Theorems.Thm_GlobalTheory_KroneckerLimit_rowSum_one
import Theorems.Thm_GlobalTheory_KroneckerLimit_hasSum_lambert
import Theorems.Thm_GlobalTheory_KroneckerLimit_betaConst_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Set
open scoped Real
open GlobalTheory GlobalTheory.KroneckerLimit
namespace GlobalTheory.KroneckerLimit
theorem _root_.solution (z : ℂ) (hz : 0 < z.im) :
    ∑' m, rowError z.re z.im m 1
      = -(2 * π / z.im) * Real.log ‖∏' k : ℕ, (1 - ModularForm.eta_q k z)‖ := by
  have hq := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨z, hz⟩
  have h := (hasSum_lambert hq).mul_left (2 * π / z.im)
  simp only [ModularForm.eta_q_eq_pow]
  rw [neg_mul, ← mul_neg]
  refine HasSum.tsum_eq (h.congr_fun fun m => ?_)
  have hY : 0 < ((m : ℝ) + 1) * z.im := by positivity
  have := rowSum_one ((m + 1) * z) (by simpa using hY)
  rw [show 2 * π * Complex.I * ((m + 1) * z) = ((m + 1 : ℕ) : ℂ) * (2 * π * Complex.I * z) by
    push_cast; ring, Complex.exp_nat_mul] at this
  have e1 : ((m + 1) * z).re = (m + 1) * z.re := by simp
  have e2 : ((m + 1) * z).im = (m + 1) * z.im := by simp
  rw [e1, e2] at this
  rw [rowError, this, betaConst_one, show (1 : ℝ) - 2 * 1 = -1 by norm_num, Real.rpow_neg_one]
  simp only
  field_simp
  ring
end GlobalTheory.KroneckerLimit
