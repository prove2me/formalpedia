-- Prove2me | solution 1 for GlobalTheory.ExpDivision.quot_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:44:47.566805+00:00
-- url     : https://prove2.me/submissions/25697fd4-2c8d-4703-ad37-9d8b5b6b0e9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityAsSumExpMinusOne
import Theorems.Thm_GlobalTheory_ExpDivision_mul_quot
import Theorems.Thm_GlobalTheory_ExpDivision_quot_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.ExpDivision
namespace GlobalTheory.ExpDivision
theorem _root_.solution (a t : ℝ) : quot (-a) t = (starRingEnd ℂ) (quot a t) := by
  by_cases ht : t = 0
  · subst ht; simp [quot_zero]
  · have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    apply mul_left_cancel₀ ht'
    have := congrArg (starRingEnd ℂ) (mul_quot a t)
    rw [map_mul, Complex.conj_ofReal] at this
    rw [this, mul_quot, map_sub, ← Complex.exp_conj]
    simp
end GlobalTheory.ExpDivision
