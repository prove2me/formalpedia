-- Prove2me | solution 1 for GlobalTheory.sum_zeta_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:43:12.283448+00:00
-- url     : https://prove2.me/submissions/20417efd-8357-40a6-b22b-7c993fc31a9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIdealInClassOfNormLeSqrtDiscr
import Theorems.Thm_GlobalTheory_sum_zeta_pow_succ_le

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
namespace GlobalTheory
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) {X : ℝ} (hX : 1 ≤ X) :
    ((∑ n ∈ Ioc 0 ⌊X⌋₊, (ζ ^ k : ArithmeticFunction ℕ) n : ℕ) : ℝ)
      ≤ X * (1 + Real.log X) ^ (k - 1) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hL : 0 ≤ 1 + Real.log X := by have := Real.log_nonneg hX; linarith
  have h := Nat.floor_le (zero_le_one.trans hX)
  refine (sum_zeta_pow_succ_le k hX _ h).trans ?_
  rw [Nat.add_sub_cancel]
  gcongr
end GlobalTheory
