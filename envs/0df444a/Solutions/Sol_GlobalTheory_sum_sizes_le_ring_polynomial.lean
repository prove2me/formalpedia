-- Prove2me | solution 1 for GlobalTheory.sum_sizes_le_ring_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:41:41.441669+00:00
-- url     : https://prove2.me/submissions/b1eafe40-e620-40b6-a670-2e945549b985

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_SumSizesLeRingPolynomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (f r m L lE lh lG : ℝ), 8 ≤ f → 62 ≤ r → 2 * m ≤ r → 0 ≤ m → 4 ≤ L → lE ≤ 2 * L → 0 ≤ lE →
      log f ≤ L → lh ≤ f * lE + 2 * f * log (1 + f * lE) → lG ≤ f * r ^ 2 * (18 * L + 2) →
      lG + (m + 5) * lh + (4 * f + 20) * (21 * L) + 100 * L
        ≤ 19 * f * r ^ 2 * L + 198 * f ^ 2 * L := by
  intro f r m L lE lh lG hf hr hm hm0 hL hE hE0 hlog hlh hlG
  have hf0 : 0 < f := by linarith
  have hL0 : 0 < L := by linarith
  have hfE0 : 0 ≤ f * lE := mul_nonneg hf0.le hE0
  have hfE : f * lE ≤ f * (2 * L) := mul_le_mul_of_nonneg_left hE hf0.le
  have hfL : 32 ≤ f * L := by nlinarith
  have h1 : log (1 + f * lE) ≤ log (f * (3 * L)) :=
    log_le_log (by linarith) (by nlinarith)
  have h2 : log (f * (3 * L)) = log f + log (3 * L) :=
    log_mul hf0.ne' (by positivity)
  have h3 : log (3 * L) ≤ 3 * L - 1 := log_le_sub_one_of_pos (by positivity)
  have h4 : log (1 + f * lE) ≤ 4 * L := by linarith
  have h5 : 2 * f * log (1 + f * lE) ≤ 2 * f * (4 * L) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  have h6 : lh ≤ 10 * (f * L) := by nlinarith
  have h7 : (m + 5) * lh ≤ (m + 5) * (10 * (f * L)) :=
    mul_le_mul_of_nonneg_left h6 (by linarith)
  have h8 : (m + 5) * (10 * (f * L)) ≤ (r / 2 + 5) * (10 * (f * L)) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h9 : f * r ^ 2 * 4 ≤ f * r ^ 2 * L :=
    mul_le_mul_of_nonneg_left hL (by positivity)
  have h10 : 8 * L ≤ f * L := mul_le_mul_of_nonneg_right hf hL0.le
  have h11 : 5 * r + 200 ≤ r ^ 2 / 2 := by nlinarith
  have h12 : (5 * r + 200) * (f * L) ≤ r ^ 2 / 2 * (f * L) :=
    mul_le_mul_of_nonneg_right h11 (by linarith)
  have h13 : 0 ≤ f ^ 2 * L := by positivity
  nlinarith
end GlobalTheory
