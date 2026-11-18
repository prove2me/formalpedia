-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_lintegral_sq_nat_count
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:03:21.38836+00:00
-- url     : https://prove2.me/submissions/97155d44-2113-4377-ac65-bd8b2d9fa79a

import Mathlib
import Theorems.Thm_ProbabilityTheory_poissonSecondMoment_hasSum
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Nat
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_lintegral_sq_nat_count (r : ℝ≥0) :
  (∫⁻ n : ℕ, ENNReal.ofReal ((n : ℝ) ^ 2) ∂(poissonMeasure r)) =
    ENNReal.ofReal ((r : ℝ) ^ 2 + r) := by
  have hs := ProbabilityTheory.poissonSecondMoment_hasSum r
  rw [lintegral_countable', ← hs.tsum_eq,
    ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs.summable]
  refine tsum_congr fun n => ?_
  rw [ENNReal.ofReal_mul (by positivity), ofReal_measureReal (measure_ne_top _ _)]
end Kyprianou.ProofPreparation

theorem solution (r : ℝ≥0) :
  (∫⁻ n : ℕ, ENNReal.ofReal ((n : ℝ) ^ 2) ∂(poissonMeasure r)) =
    ENNReal.ofReal ((r : ℝ) ^ 2 + r) :=
  Kyprianou.ProofPreparation.poisson_lintegral_sq_nat_count r
