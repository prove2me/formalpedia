-- Prove2me | solution 1 for GlobalTheory.ceSum_small_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:26:05.640803+00:00
-- url     : https://prove2.me/submissions/a2aecfa1-f19a-4696-b023-22edd4b7921a

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CmValuesExponentLogSumLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) (n : ℕ) :
    ∑ l ∈ S, (if l ≤ n then Real.log l else 0) ≤ n * Real.log 4 := by
  rw [← Finset.sum_filter]
  calc ∑ l ∈ S.filter (· ≤ n), Real.log (l : ℝ)
      ≤ ∑ l ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log (l : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun l hl _ => ?_
        · intro l hl
          rcases Finset.mem_filter.1 hl with ⟨hlS, hln⟩
          exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hS l hlS⟩
        · exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.1 hl).2.one_lt.le)
    _ = Real.log (primorial n : ℝ) := by
        rw [primorial, Nat.cast_prod, Real.log_prod]
        intro l hl
        exact_mod_cast (Finset.mem_filter.1 hl).2.ne_zero
    _ ≤ Real.log ((4 : ℝ) ^ n) := by
        apply Real.log_le_log (by exact_mod_cast primorial_pos n)
        exact_mod_cast primorial_le_four_pow n
    _ = n * Real.log 4 := by rw [Real.log_pow]
end GlobalTheory
