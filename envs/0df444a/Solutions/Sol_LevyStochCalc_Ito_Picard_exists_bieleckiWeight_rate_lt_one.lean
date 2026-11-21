-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.exists_bieleckiWeight_rate_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T02:54:45.706178+00:00
-- url     : https://prove2.me/submissions/39734fc0-5e31-481e-9653-e51772ac1886

import Mathlib
open scoped NNReal ENNReal Topology
variable {n d : ℕ} {T : ℝ}
theorem solution (L : ℝ) (hT : 0 < T) :
    ∃ β : ℝ, 0 < β ∧
      (ENNReal.ofReal
        ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
          / (2 * β))) ^ ((1 : ℝ) / 2) < 1 := by
  let A : ℝ := 3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A + 1, by linarith, ?_⟩
  change (ENNReal.ofReal (A / (2 * (A + 1)))) ^ ((1 : ℝ) / 2) < 1
  have hden : 0 < 2 * (A + 1) := by linarith
  have hlt : A / (2 * (A + 1)) < 1 := (div_lt_iff₀ hden).mpr (by linarith)
  have h : ENNReal.ofReal (A / (2 * (A + 1))) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).2 hlt
  rw [← ENNReal.one_rpow ((1 : ℝ) / 2)]
  exact ENNReal.rpow_lt_rpow h (by norm_num)
