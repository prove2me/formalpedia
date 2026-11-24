-- Prove2me | solution 1 for GlobalTheory.minkowski_const_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:46:19.704858+00:00
-- url     : https://prove2.me/submissions/e4c3ecc5-e803-4b79-bf83-6eb1b47e58f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIdealInClassOfNormLeSqrtDiscr
import Theorems.Thm_GlobalTheory_two_pow_mul_factorial_succ_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Real NumberField ArithmeticFunction.zeta
open Module NumberField Finset
open GlobalTheory
variable (K : Type*) [Field K] [NumberField K]
namespace GlobalTheory
theorem _root_.solution :
    (4 / π) ^ InfinitePlace.nrComplexPlaces K *
      (((finrank ℚ K).factorial : ℝ) / (finrank ℚ K : ℝ) ^ finrank ℚ K) ≤ 1 := by
  have hr := InfinitePlace.card_add_two_mul_card_eq_rank K
  have hpos : 0 < finrank ℚ K := finrank_pos
  obtain ⟨n, hn⟩ : ∃ n, finrank ℚ K = n + 1 := ⟨finrank ℚ K - 1, by omega⟩
  rw [hn] at hr ⊢
  have h1 : (4 / π) ^ InfinitePlace.nrComplexPlaces K ≤ (2 : ℝ) ^ n := by
    have h4 : 4 / π ≤ 2 := by
      rw [div_le_iff₀ Real.pi_pos]; linarith [Real.pi_gt_three]
    calc _ ≤ (2 : ℝ) ^ InfinitePlace.nrComplexPlaces K := by gcongr
      _ ≤ _ := pow_le_pow_right₀ one_le_two (by omega)
  have h2 := two_pow_mul_factorial_succ_le n
  rw [← mul_div_assoc, div_le_one (by positivity)]
  push_cast
  refine le_trans ?_ h2
  gcongr
end GlobalTheory
