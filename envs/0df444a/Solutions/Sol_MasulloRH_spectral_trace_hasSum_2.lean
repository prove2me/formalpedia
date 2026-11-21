-- Prove2me | solution 2 for MasulloRH.spectral_trace_hasSum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-20T22:24:20.967317+00:00
-- url     : https://prove2.me/submissions/767deb43-2fef-4977-81db-9a1e88500079
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_trace_window_comparison
import Theorems.Thm_MasulloRH_archTerm_log_test_eq_neg_real_place
import Theorems.Thm_MasulloRH_narrow_window_omitted_zero_sum

set_option autoImplicit false
open MasulloRH MeasureTheory Set

theorem solution (α : ℝ) (hα : 0 < α) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    HasSum (zetaTraceTerm φ α) ((mellin φ (1 / 2) + mellin φ (-1 / 2)) -
      ((∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) + ∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i)) := by
  let outside := {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | α ≤ |ρ.val.re - 1/2|}
  have hout : (∑' r : outside, (ConnesRZ.zeroMult r.val.val : ℂ) * mellin φ (r.val.val - 1/2)) = 0 := by
    by_cases hn : α < 1/2
    · exact narrow_window_omitted_zero_sum α hα hn φ hφ
    · have : IsEmpty outside := ⟨fun r => by
        have hstrip := r.val.prop
        have hr : α ≤ |r.val.val.re - 1/2| := r.prop
        exact (not_lt_of_ge hr) ((abs_lt.mpr ⟨by linarith [hstrip.2.1], by linarith [hstrip.2.2]⟩).trans_le (le_of_not_gt hn))⟩
      exact tsum_empty
  obtain ⟨_, _, hsum, _, hbalance⟩ := trace_window_comparison α φ hφ
  rw [archTerm_log_test_eq_neg_real_place φ hφ] at hbalance
  change _ + _ + (∑' r : outside, _) = _ at hbalance
  rw [hout, add_zero] at hbalance
  convert hsum.hasSum using 1
  linear_combination -hbalance
