-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.eventual_fixed_minor_analytic_upper_bound_analyticAggregate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T17:54:58.047762+00:00
-- url     : https://prove2.me/submissions/852a8c0e-617a-42d9-85f5-2edb6c903939
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_analytic_remainder_candidate_tendsto_zero
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_minor_candidate_analytic_bound
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution
    (nu : Real) (d : FixedData nu) :
    ∃ error : Real → Real, Tendsto error atTop (𝓝 0) ∧
      ∀ᶠ H : Real in atTop, ∀ selection : Row d H → Column d H,
        (actualMinor d H selection).det ≠ 0 →
          Real.log ‖(actualMinor d H selection).det‖ /
              ((actualRowCount d H : Real) * H) ≤
            d.analyticError + error H +
              max (-collisionRate d H)
                (-nu * ((d.base.A : Real) * (1 - d.base.eta) -
                  actualMean d H)) := by
  refine ⟨fun H =>
      (Real.log (actualRowCount d H : Real) + Real.log 2 / 4 -
        Real.log (1 - Real.exp (-Real.log 2 / 2)) +
        Real.log ((H + 1) ^ (2 * d.m) * (H / (d.v0 : Real) + 1))) / H,
      ?_, ?_⟩
  · exact analytic_remainder_candidate_tendsto_zero d
  · filter_upwards [eventually_gt_atTop (0 : Real)] with H hH
    intro selection hne
    exact actual_minor_candidate_analytic_bound d hH selection hne