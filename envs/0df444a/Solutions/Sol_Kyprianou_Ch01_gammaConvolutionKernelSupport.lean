-- Prove2me | solution 1 for Kyprianou.Ch01.gammaConvolutionKernelSupport
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T08:27:05.371052+00:00
-- url     : https://prove2.me/submissions/ee8fec3f-2e41-4f82-a318-a2dd17168200

import Mathlib.Probability.Distributions.Gamma
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

theorem solution (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) (z : ℝ) (hz : 0 ≤ z) (x : ℝ) :
    LevyFoundations.arrivalGammaDensity beta n x *
      LevyFoundations.arrivalGammaDensity beta 0 (z - x) =
    (Set.Icc (0 : ℝ) z).indicator
      (fun y : ℝ => ENNReal.ofReal
        ((beta ^ (n + 2) * Real.exp (-(beta * z)) /
          (n.factorial : ℝ)) * y ^ n)) x := by
  unfold LevyFoundations.arrivalGammaDensity
    LevyFoundations.arrivalGammaDensityReal
  let c : ℝ := beta ^ (n + 2) * Real.exp (-(beta * z)) /
    (n.factorial : ℝ)
  change ((Ici (0 : ℝ)).indicator
    (fun y => ENNReal.ofReal
      (beta ^ (n + 1) * y ^ n * Real.exp (-(beta * y)) /
        (n.factorial : ℝ))) x) *
    ((Ici (0 : ℝ)).indicator
      (fun y => ENNReal.ofReal
        (beta ^ (0 + 1) * y ^ 0 * Real.exp (-(beta * y)) /
          (Nat.factorial 0 : ℝ))) (z - x)) =
    (Icc (0 : ℝ) z).indicator
      (fun y => ENNReal.ofReal (c * y ^ n)) x
  by_cases hx : x ∈ Icc (0 : ℝ) z
  · have hx0 : x ∈ Ici (0 : ℝ) := hx.1
    have hzx : z - x ∈ Ici (0 : ℝ) := by
      change 0 ≤ z - x
      linarith [hx.2]
    rw [Set.indicator_of_mem hx0,
      Set.indicator_of_mem hzx, Set.indicator_of_mem hx]
    have hx_nonneg : 0 ≤ x := hx.1
    have hfirst : 0 ≤ beta ^ (n + 1) * x ^ n *
        Real.exp (-(beta * x)) / (n.factorial : ℝ) := by positivity
    rw [← ENNReal.ofReal_mul hfirst]
    congr 1
    dsimp [c]
    have he : Real.exp (-(beta * x)) *
        Real.exp (-(beta * (z - x))) = Real.exp (-(beta * z)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← he]
    push_cast
    ring
  · rw [Set.indicator_of_notMem hx]
    by_cases hx0 : 0 ≤ x
    · have hzx : z - x ∉ Ici (0 : ℝ) := by
        intro h
        apply hx
        constructor
        · exact hx0
        · change 0 ≤ z - x at h
          linarith
      rw [Set.indicator_of_notMem hzx, mul_zero]
    · have hneg : x ∉ Ici (0 : ℝ) := not_le.mpr (lt_of_not_ge hx0)
      rw [Set.indicator_of_notMem hneg, zero_mul]
