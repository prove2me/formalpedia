-- Prove2me | solution 1 for Kyprianou.Ch01.pmfNatWeightedPowersSummable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T07:37:54.547877+00:00
-- url     : https://prove2.me/submissions/b69c3a54-0d4b-4212-866f-96eb4d0a5f09

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal
set_option autoImplicit false

theorem solution
    (p : PMF ℕ) (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Summable (fun n : ℕ => z ^ n * (p n).toReal) := by
  have hsum : Summable (fun n : ℕ => (p n).toReal) :=
    ENNReal.summable_toReal p.tsum_coe_ne_top
  apply Summable.of_nonneg_of_le
  · intro n
    exact mul_nonneg (pow_nonneg hz0 _) ENNReal.toReal_nonneg
  · intro n
    calc
      z ^ n * (p n).toReal ≤ 1 * (p n).toReal :=
        mul_le_mul_of_nonneg_right
          (pow_le_one₀ hz0 hz1) ENNReal.toReal_nonneg
      _ = (p n).toReal := one_mul _
  · exact hsum
