-- Prove2me | solution 1 for Kyprianou.Ch01.logarithmicJumpCharFunWeights
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:20:25.214058+00:00
-- url     : https://prove2.me/submissions/c4f2cc93-e82a-44bd-8e3d-505f63d934e5

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Theorems.Thm_Kyprianou_Ch01_shiftedPMFCharFun_tsum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex
set_option autoImplicit false

/-! Identify the logarithmic jump law's Fourier weights exactly. -/
theorem solution
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (jump : PMF ℕ)
    (hjump : ∀ n : ℕ,
      jump n = ENNReal.ofReal
        ((q ^ (n + 1) / ((n : ℝ) + 1)) / (-Real.log (1 - q))))
    (xi : ℝ) :
    charFun (jump.toMeasure.map
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ))) xi =
      ∑' n : ℕ,
        ((q ^ (n + 1) / ((n : ℝ) + 1)) / (-Real.log (1 - q))) •
          Complex.exp
            ((xi : ℂ) * (((n + 1 : ℕ) : ℝ) : ℂ) * Complex.I) := by
  rw [Kyprianou.Ch01.shiftedPMFCharFun_tsum jump xi]
  have hlog : 0 < -Real.log (1 - q) := by
    have hpos : 0 < 1 - q := sub_pos.mpr hq1
    have hlt : 1 - q < 1 := sub_lt_self 1 hq0
    exact neg_pos.mpr (Real.log_neg hpos hlt)
  apply tsum_congr
  intro n
  have hn : 0 ≤
      (q ^ (n + 1) / ((n : ℝ) + 1)) / (-Real.log (1 - q)) :=
    div_nonneg
      (div_nonneg (pow_nonneg (le_of_lt hq0) _) (by positivity))
      (le_of_lt hlog)
  rw [hjump n, ENNReal.toReal_ofReal hn]
