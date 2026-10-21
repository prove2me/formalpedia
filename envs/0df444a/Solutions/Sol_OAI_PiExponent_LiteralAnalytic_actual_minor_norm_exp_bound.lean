-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.actual_minor_norm_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T02:36:16.945181+00:00
-- url     : https://prove2.me/submissions/f9e4c657-433a-4f59-9d3e-f0a509326418

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actual_minor_bound_from_expansion
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actual_minor_bounded_expansion

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) :
    ‖(actualMinor d H selection).det‖ ≤ Real.exp (((actualRowCount d H : ℝ) * H) *
      (d.analyticError + analyticRemainder d H +
        max (-collisionRate d H)
          (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)))) := by
  obtain ⟨N, terms, hexp, hcount, hterms⟩ :=
    OAI.PiExponent.LiteralAnalytic.actual_minor_bounded_expansion
      d hnu hH selection
  exact OAI.PiExponent.LiteralAnalytic.actual_minor_bound_from_expansion
    d hnu hH selection N terms hexp hcount hterms