-- Prove2me | solution 1 for Kyprianou.Ch01.gammaArrivalPointwiseENNRealSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T08:16:19.355373+00:00
-- url     : https://prove2.me/submissions/8e77caf2-6326-4f06-bb72-993687b8cdb6

import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_levy_foundations_arrivalGammaDensity
import Theorems.Thm_Kyprianou_Ch01_gammaDensityRealSeries
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- The arrival-density renewal sum is a constant rate on the positive half-line. -/
theorem solution (beta z : ℝ) (hbeta : 0 < beta) (hz : 0 ≤ z) :
    (∑' n : ℕ, LevyFoundations.arrivalGammaDensity beta n z) =
      ENNReal.ofReal beta := by
  let a : ℕ → ℝ := fun n =>
    beta ^ (n + 1) * z ^ n * Real.exp (-beta * z) / (n.factorial : ℝ)
  have hf (n : ℕ) :
      LevyFoundations.arrivalGammaDensity beta n z = ENNReal.ofReal (a n) := by
    simp [a, LevyFoundations.arrivalGammaDensity,
      LevyFoundations.arrivalGammaDensityReal, hz]
  have han (n : ℕ) : 0 ≤ a n := by
    dsimp [a]; positivity
  have hs0 : Summable (fun n : ℕ =>
      (beta * z) ^ n / (n.factorial : ℝ)) := by
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (NormedSpace.expSeries_summable' (𝕂 := ℝ) (beta * z))
  have heq : a = fun n : ℕ =>
      (beta * Real.exp (-beta * z)) *
        ((beta * z) ^ n / (n.factorial : ℝ)) := by
    funext n
    dsimp [a]
    rw [pow_succ, mul_pow]
    ring
  have hs : Summable a := by
    rw [heq]
    exact hs0.mul_left _
  calc
    (∑' n : ℕ, LevyFoundations.arrivalGammaDensity beta n z) =
        ∑' n : ℕ, ENNReal.ofReal (a n) := by
      apply tsum_congr
      intro n
      exact hf n
    _ = ENNReal.ofReal (∑' n : ℕ, a n) :=
        (ENNReal.ofReal_tsum_of_nonneg han hs).symm
    _ = ENNReal.ofReal beta := by
      congr 1
      exact Kyprianou.Ch01.gammaDensityRealSeries beta z hbeta hz
