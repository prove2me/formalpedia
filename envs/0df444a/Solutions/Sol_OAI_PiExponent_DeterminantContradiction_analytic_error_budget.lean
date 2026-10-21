-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.analytic_error_budget
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:00:25.873994+00:00
-- url     : https://prove2.me/submissions/f0459638-39b1-40eb-af8b-e41230eb6b03

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

/-- The analytic and arithmetic error budgets add up to less than `epsilon`. -/
theorem solution {nu : ℝ} (d : FixedData nu) :
    d.analyticError + d.arithmeticError < d.epsilon := by
  have h1 := d.initial_margin
  have h2 := d.dimension_margin
  have h3 := d.weight_margin
  have h3' : Arithmetic.lcmConstant * (∑ i : Fin d.m, 1 / d.x (i.val + 1)) +
      ((d.base.theta : ℝ) + Real.log 4 + Real.log (2 * (d.K : ℝ)) + nu +
        Real.log (200 * (d.K : ℝ))) / d.wstar < d.epsilon / 3 := by
    simpa [OAI.PiExponent.weightErrorCoefficient] using h3
  have hsum : d.analyticError + d.arithmeticError =
      nu / d.F0 +
        ((Arithmetic.lcmConstant * d.F0 * (d.m : ℝ) + 2 * Real.log 2) / (d.v0 : ℝ) +
          100 * (d.K : ℝ) / (d.w0 : ℝ)) +
        (Arithmetic.lcmConstant * (∑ i : Fin d.m, 1 / d.x (i.val + 1)) +
          ((d.base.theta : ℝ) + Real.log 4 + Real.log (2 * (d.K : ℝ)) + nu +
            Real.log (200 * (d.K : ℝ))) / d.wstar) := by
    unfold AdmissibleParameters.analyticError AdmissibleParameters.translationError
      AdmissibleParameters.holomorphicError AdmissibleParameters.arithmeticError
    ring
  rw [hsum]
  linarith [h1, h2, h3']
