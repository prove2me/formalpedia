-- Prove2me | solution 1 for GlobalTheory.ValCompletion.not_pow_succ_dvd_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:08:29.016613+00:00
-- url     : https://prove2.me/submissions/f69e790c-f0b4-4ca4-b951-50713411d384

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionValuationRingCompleteValuationDoma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory GlobalTheory.ValCompletion
variable {V : Type} [CommRing V] [IsDomain V] [ValuationRing V] {x : V}
namespace GlobalTheory.ValCompletion
theorem _root_.solution (hx0 : x ≠ 0) (hxu : ¬ IsUnit x) (m : ℕ) : ¬ x ^ (m + 1) ∣ x ^ m := by
  rintro ⟨c, hc⟩
  apply hxu
  have h : x ^ m * 1 = x ^ m * (x * c) := by rw [mul_one]; nth_rewrite 1 [hc]; ring
  exact IsUnit.of_mul_eq_one c (mul_left_cancel₀ (pow_ne_zero m hx0) h).symm
end GlobalTheory.ValCompletion
