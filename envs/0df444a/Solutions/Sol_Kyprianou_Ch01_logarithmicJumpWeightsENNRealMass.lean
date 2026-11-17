-- Prove2me | solution 1 for Kyprianou.Ch01.logarithmicJumpWeightsENNRealMass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:57:13.730203+00:00
-- url     : https://prove2.me/submissions/22382325-710d-4481-9868-9f5b70a7c3b7

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Tactic.Positivity
import Theorems.Thm_Kyprianou_Ch01_logarithmicJumpWeightsHasSumOne
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
set_option autoImplicit false

/-! Extended-nonnegative normalisation of the logarithmic jump distribution. -/
theorem solution
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    (∑' n : ℕ,
      ENNReal.ofReal
        ((q ^ (n + 1) / ((n : ℝ) + 1)) / (-Real.log (1 - q)))) = 1 := by
  let f : ℕ → ℝ := fun n =>
    (q ^ (n + 1) / ((n : ℝ) + 1)) / (-Real.log (1 - q))
  have hpos : 0 < -Real.log (1 - q) := by
    have h1 : 0 < 1 - q := sub_pos.mpr hq1
    have hlt : 1 - q < 1 := sub_lt_self 1 hq0
    exact neg_pos.mpr (Real.log_neg h1 hlt)
  have hnonneg : ∀ n : ℕ, 0 ≤ f n := by
    intro n
    dsimp [f]
    exact div_nonneg
      (div_nonneg (pow_nonneg (le_of_lt hq0) _) (by positivity))
      (le_of_lt hpos)
  have hreal : HasSum f 1 :=
    Kyprianou.Ch01.logarithmicJumpWeightsHasSumOne q hq0 hq1
  change (∑' n : ℕ, ENNReal.ofReal (f n)) = 1
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hreal.summable]
  rw [hreal.tsum_eq]
  norm_num
