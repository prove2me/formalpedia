-- Prove2me | solution 2 for GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:38:48.123067+00:00
-- url     : https://prove2.me/submissions/9999e53a-93ab-4924-9efc-06d1df40fe94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumRangeMulOfPeriodic
import Theorems.Thm_GlobalTheory_PeriodicSumShift_periodic_shift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PeriodicSumShift
namespace GlobalTheory.PeriodicSumShift
theorem _root_.solution : ∀ {K : Type} [inst : Field K] (g : ℕ → K) (N : ℕ),
    (∀ (i : ℕ), g (N + i) = g i) → ∀ (k : ℕ),
      ∑ i ∈ Finset.range (N * k), g i = (↑k : K) * ∑ i ∈ Finset.range N, g i := by
  intro K _ g N h k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp_rw [periodic_shift g N h k]
    push_cast; ring
end GlobalTheory.PeriodicSumShift
