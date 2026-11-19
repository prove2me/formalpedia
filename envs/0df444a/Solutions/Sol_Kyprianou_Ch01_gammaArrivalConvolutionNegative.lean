-- Prove2me | solution 1 for Kyprianou.Ch01.gammaArrivalConvolutionNegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T08:12:17.870667+00:00
-- url     : https://prove2.me/submissions/0a1b7685-d545-4dad-8a97-2437655fb224

import Mathlib.Probability.Distributions.Gamma
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Definitions.Def_levy_foundations_arrivalGammaDensity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    (beta : ℝ) (hbeta : 0 < beta)
    (n : ℕ) (z : ℝ) (hz : z < 0) :
    (∫⁻ x : ℝ, LevyFoundations.arrivalGammaDensity beta n x *
      LevyFoundations.arrivalGammaDensity beta 0 (z - x)) = 0 := by
  unfold LevyFoundations.arrivalGammaDensity
    LevyFoundations.arrivalGammaDensityReal
  have hzero (x : ℝ) :
      ((Ici (0 : ℝ)).indicator
        (fun y => ENNReal.ofReal
          (beta ^ (n + 1) * y ^ n * Real.exp (-(beta * y)) /
            (n.factorial : ℝ))) x) *
      ((Ici (0 : ℝ)).indicator
        (fun y => ENNReal.ofReal
          (beta ^ (0 + 1) * y ^ 0 * Real.exp (-(beta * y)) /
            (Nat.factorial 0 : ℝ))) (z - x)) = 0 := by
    by_cases hx : 0 ≤ x
    · have hzx : z - x ∉ Ici (0 : ℝ) := by
        change ¬ 0 ≤ z - x
        intro h
        linarith
      rw [Set.indicator_of_notMem hzx, mul_zero]
    · have hxm : x ∉ Ici (0 : ℝ) := not_le.mpr (lt_of_not_ge hx)
      rw [Set.indicator_of_notMem hxm, zero_mul]
  simp_rw [hzero]
  exact lintegral_zero
