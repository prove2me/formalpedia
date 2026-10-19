-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.eventual_actual_mean_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T22:51:33.98426+00:00
-- url     : https://prove2.me/submissions/f8a5ce73-52c3-4987-b88e-4413ced49ee6

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution {nu : ℝ} (d : FixedData nu) :
    ∀ᶠ H : ℝ in atTop, 0 ≤ actualMean d H := by
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
  rw [actualMean, MatrixArithmetic.meanRowWeight,
    MatrixArithmetic.rowWeightedSum]
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro ρ hρ
    apply Finset.sum_nonneg
    intro i hi
    simp only [MatrixArithmetic.logWeights]
    positivity
  · positivity