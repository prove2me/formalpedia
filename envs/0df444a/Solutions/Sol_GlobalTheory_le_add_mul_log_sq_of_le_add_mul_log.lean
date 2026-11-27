-- Prove2me | solution 1 for GlobalTheory.le_add_mul_log_sq_of_le_add_mul_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:39:38.220085+00:00
-- url     : https://prove2.me/submissions/83b0d403-a27a-4d70-a0e3-517094cdf48f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeAddMulLogSqOfLeAddMulLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (α β r s : ℝ), 0 ≤ α → 0 ≤ β → 1 ≤ r → r ≤ s → s ≤ α + β * Real.log r →
      s ≤ α + β * Real.log ((α + 2 * β + 1) ^ 2) := by
  intro α β r s hα hβ hr hrs hs
  have hr0 : 0 < r := by linarith
  set t := Real.sqrt r with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg r
  have htt : t * t = r := Real.mul_self_sqrt hr0.le
  have ht1 : 1 ≤ t := by
    by_contra h
    push_neg at h
    nlinarith
  have htpos : 0 < t := by linarith
  have hlog : Real.log r ≤ 2 * t - 2 := by
    have h1 : Real.log r = 2 * Real.log t := by
      rw [← htt, Real.log_mul htpos.ne' htpos.ne']; ring
    have h2 := Real.log_le_sub_one_of_pos htpos
    linarith
  have hle : t ≤ α + 2 * β + 1 := by
    by_contra h
    push_neg at h
    nlinarith [mul_lt_mul_of_pos_left h htpos, mul_nonneg hα (sub_nonneg.mpr ht1),
      mul_le_mul_of_nonneg_left hlog hβ]
  have hrc : r ≤ (α + 2 * β + 1) ^ 2 := by
    rw [← htt]; nlinarith
  have hl : Real.log r ≤ Real.log ((α + 2 * β + 1) ^ 2) := Real.log_le_log hr0 hrc
  nlinarith [mul_le_mul_of_nonneg_left hl hβ]
end GlobalTheory
