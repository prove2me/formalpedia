-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.eventual_determinant_exponent_branch
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T22:24:56.904413+00:00
-- url     : https://prove2.me/submissions/2a31ebfa-9c51-461e-9b92-247c69c53684

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_analytic_error_budget
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventual_actual_mean_le_theta
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_analytic_remainder_tendsto_zero

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 2 < nu) :
    ∀ᶠ H : ℝ in atTop,
      d.analyticError + analyticRemainder d H +
          (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)) <
        -(1 - actualMean d H) - d.arithmeticError := by
  have herr := OAI.PiExponent.DeterminantContradiction.analytic_error_budget d
  have hmean := OAI.PiExponent.DeterminantContradiction.eventual_actual_mean_le_theta d
  have hrem := OAI.PiExponent.DeterminantContradiction.analytic_remainder_tendsto_zero d
  let gap : ℝ := nu * ((d.base.A : ℝ) * (1 - d.base.eta) - d.base.theta) - (1 - d.base.theta)
  have heps : d.epsilon < gap := by
    simpa [gap] using d.epsilon_lt_gap
  have hpos : 0 < gap - d.epsilon := by linarith
  have hsmall : ∀ᶠ H : ℝ in atTop, analyticRemainder d H < gap - d.epsilon := by
    have hmem : (0 : ℝ) ∈ Set.Iio (gap - d.epsilon) := by simpa [Set.mem_Iio] using hpos
    filter_upwards [hrem.eventually (IsOpen.mem_nhds isOpen_Iio hmem)] with H hH
    exact hH
  filter_upwards [hmean, hsmall] with H hm hr
  have hmul : (nu - 1) * actualMean d H ≤ (nu - 1) * d.base.theta :=
    mul_le_mul_of_nonneg_left hm (by linarith)
  have hcombined : d.analyticError + d.arithmeticError + analyticRemainder d H < gap := by
    linarith
  dsimp [gap] at hcombined ⊢
  nlinarith