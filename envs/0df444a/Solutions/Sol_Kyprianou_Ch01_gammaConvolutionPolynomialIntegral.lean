-- Prove2me | solution 1 for Kyprianou.Ch01.gammaConvolutionPolynomialIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T08:16:36.960903+00:00
-- url     : https://prove2.me/submissions/9df8ffd8-6dd2-4a69-bd6f-ab654e171597

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

theorem solution (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    (∫⁻ x in Set.Icc (0 : ℝ) z,
      ENNReal.ofReal
        ((beta ^ (n + 2) * Real.exp (-(beta * z)) /
          (n.factorial : ℝ)) * x ^ n)) =
      LevyFoundations.arrivalGammaDensity beta (n + 1) z := by
  unfold LevyFoundations.arrivalGammaDensity
    LevyFoundations.arrivalGammaDensityReal
  let c : ℝ := beta ^ (n + 2) * Real.exp (-(beta * z)) /
    (n.factorial : ℝ)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  change (∫⁻ x in Set.Icc (0 : ℝ) z,
    ENNReal.ofReal (c * x ^ n)) =
      (Ici (0 : ℝ)).indicator
        (fun y => ENNReal.ofReal
          (beta ^ ((n + 1) + 1) * y ^ (n + 1) *
            Real.exp (-(beta * y)) / ((n + 1).factorial : ℝ))) z
  have hint : IntegrableOn (fun x : ℝ => c * x ^ n) (Icc 0 z) :=
    (by fun_prop : Continuous fun x : ℝ => c * x ^ n).integrableOn_Icc
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) z)] (fun x : ℝ => c * x ^ n) :=
    (ae_restrict_iff' measurableSet_Icc).mpr
      (Filter.Eventually.of_forall fun x hx => by
        have hp : 0 ≤ x := hx.1
        positivity)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hz,
    intervalIntegral.integral_const_mul, integral_pow]
  have hzmem : z ∈ Ici (0 : ℝ) := hz
  rw [Set.indicator_of_mem hzmem]
  congr 1
  dsimp [c]
  push_cast [Nat.factorial_succ]
  field_simp
  ring
