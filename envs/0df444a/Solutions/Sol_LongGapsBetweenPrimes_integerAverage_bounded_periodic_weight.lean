-- Prove2me | solution 1 for LongGapsBetweenPrimes.integerAverage_bounded_periodic_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:06:03.547318+00:00
-- url     : https://prove2.me/submissions/1b54ef4e-95ba-4520-b4d4-cefdd370dde7

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_integerAverage_period_error
import Theorems.Thm_LongGapsBetweenPrimes_integerAverage_weight_error
import Theorems.Thm_LongGapsBetweenPrimes_mod_invariant_of_dvd

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {ι : Type*} [Fintype ι]
    {q T : ℕ} (hq : 0 < q) (hT : 0 < T) {D : ℝ} (hD : 0 ≤ D)
    (period : ι → ℕ) (hperiod_pos : ∀ i, 0 < period i) (hperiod_q : ∀ i, period i ∣ q)
    (hperiod_D : ∀ i, (period i : ℝ) ≤ D)
    (c : ι → ℝ) (hc : ∀ i, |c i| ≤ 1) (f : ι → ℕ → ℝ)
    (hf : ∀ i n, |f i n| ≤ 1) (hmod : ∀ i n, f i (n % period i) = f i n) :
    |integerAverage T (fun n => (∑ i, c i * f i n) ^ 2) -
      integerAverage q (fun n => (∑ i, c i * f i n) ^ 2)| ≤
        (Fintype.card ι : ℝ) ^ 2 * (D ^ 2 / T) := by
  apply integerAverage_weight_error q T c hc
  intro i j
  have hbound : (Nat.lcm (period i) (period j) : ℝ) ≤ D ^ 2 := by
    calc
      _ ≤ (period i : ℝ) * period j := by
        exact_mod_cast Nat.lcm_le_mul (hperiod_pos i) (hperiod_pos j)
      _ ≤ D * D := mul_le_mul (hperiod_D i) (hperiod_D j) (Nat.cast_nonneg _) hD
      _ = D ^ 2 := (pow_two D).symm
  refine (integerAverage_period_error
    (Nat.lcm_pos (hperiod_pos i) (hperiod_pos j)) hq hT
    (Nat.lcm_dvd (hperiod_q i) (hperiod_q j))
    (fun n => f i n * f j n) ?_ ?_).trans
      (div_le_div_of_nonneg_right hbound (Nat.cast_nonneg T))
  · intro n
    rw [mod_invariant_of_dvd (Nat.dvd_lcm_left _ _) (f i) (hmod i),
      mod_invariant_of_dvd (Nat.dvd_lcm_right _ _) (f j) (hmod j)]
  · intro n
    rw [abs_mul]
    exact mul_le_one₀ (hf i n) (abs_nonneg _) (hf j n)
end LongGapsBetweenPrimes
