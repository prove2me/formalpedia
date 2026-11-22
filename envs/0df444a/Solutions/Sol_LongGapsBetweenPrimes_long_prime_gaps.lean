-- Prove2me | solution 1 for LongGapsBetweenPrimes.long_prime_gaps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:25:14.0229+00:00
-- url     : https://prove2.me/submissions/10e6a481-625a-43f5-8ed3-7690622d0f3c

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_eventually_coverScale_div_eight
import Theorems.Thm_LongGapsBetweenPrimes_gapScale_eq_coverScale_log
import Theorems.Thm_LongGapsBetweenPrimes_long_gap_theorem
import Theorems.Thm_LongGapsBetweenPrimes_consecutivePrimes_eq_nth

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X → ∃ n : ℕ,
      (Nat.nth Nat.Prime (n + 1) : ℝ) < X ∧
        c * (Real.log X * Real.log (Real.log X) ^ 2 *
          Real.log (Real.log (Real.log (Real.log X))) /
            Real.log (Real.log (Real.log X)) ^ 2) <
          (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n := by
  obtain ⟨c, hc, hgap⟩ := long_gap_theorem
  have hlog : Filter.Tendsto (fun X : ℝ => Real.log X / 8)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num) Real.tendsto_log_atTop
  have heventually : ∀ᶠ X : ℝ in Filter.atTop, ∃ n : ℕ,
      (Nat.nth Nat.Prime (n + 1) : ℝ) < X ∧
        (c / 128) * gapScale X <
          (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n := by
    filter_upwards [(Real.tendsto_exp_atTop.comp hlog).eventually hgap,
      Real.tendsto_log_atTop.eventually eventually_coverScale_div_eight,
      Filter.eventually_gt_atTop (1 : ℝ)] with X hgap hscale hX
    obtain ⟨p, q, hpq, hq, hwidth⟩ := hgap
    obtain ⟨n, hn, hn'⟩ := consecutivePrimes_eq_nth hpq
    refine ⟨n, ?_, ?_⟩
    · rw [hn']
      apply hq.trans_lt
      calc
        Real.exp (Real.log X / 8) < Real.exp (Real.log X) := by
          apply Real.exp_lt_exp.mpr
          have := Real.log_pos hX
          linarith
        _ = X := Real.exp_log (by linarith)
    · rw [hn, hn', gapScale_eq_coverScale_log]
      rw [gapScale_eq_coverScale_log, Function.comp_apply, Real.log_exp,
        Nat.cast_sub hpq.2.2.1.le] at hwidth
      have hpositive : (0 : ℝ) < (q : ℝ) - p :=
        sub_pos.mpr (by exact_mod_cast hpq.2.2.1)
      have hbound := mul_le_mul_of_nonneg_left hscale hc.le
      nlinarith
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp heventually
  exact ⟨c / 128, X₀, by positivity, hX₀⟩
end LongGapsBetweenPrimes
