-- Prove2me | solution 1 for GlobalTheory.coordsDiag_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:33:52.051994+00:00
-- url     : https://prove2.me/submissions/63bea2c3-f029-4b1d-b5e8-e2d416ee4268

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAntilinearNormalForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (a b y : ℂ) (h : ‖b‖ < ‖a‖) (hy : a * y + b * starRingEnd ℂ y = 0) : y = 0 := by
  by_contra hne
  have h1 : ‖a * y‖ = ‖b * starRingEnd ℂ y‖ := by
    rw [eq_neg_of_add_eq_zero_left hy, norm_neg]
  rw [norm_mul, norm_mul, Complex.norm_conj] at h1
  have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hne
  have h2 := mul_right_cancel₀ hy'.ne' h1
  linarith
end GlobalTheory
