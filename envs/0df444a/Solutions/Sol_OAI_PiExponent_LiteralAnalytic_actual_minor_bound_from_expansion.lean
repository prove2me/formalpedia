-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.actual_minor_bound_from_expansion
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:05:23.450215+00:00
-- url     : https://prove2.me/submissions/f1e8ca66-6418-4e5a-87ea-3f3aae95d58c

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

/-- Aggregation step: if the determinant is a finite sum of `N` terms, `N` is exponentially
bounded by the number of translation choices, and each term is exponentially bounded by the
analytic/collision envelope, then the determinant itself obeys the same exponential bound
(with the analytic remainder replacing the collision remainder). -/
theorem solution {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (N : ℕ) (terms : Fin N → ℂ)
    (hexp : (actualMinor d H selection).det = ∑ i, terms i)
    (hcount : (N : ℝ) ≤ Real.exp ((actualRowCount d H : ℝ) *
      Real.log (translationTermCount d.m d.v0 H : ℝ)))
    (hterms : ∀ i, ‖terms i‖ ≤ Real.exp (((actualRowCount d H : ℝ) * H) *
      (d.analyticError + Collision.collisionRemainder (actualRowCount d H) H +
        max (-collisionRate d H)
          (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H))))) :
    ‖(actualMinor d H selection).det‖ ≤
      Real.exp (((actualRowCount d H : ℝ) * H) *
        (d.analyticError + analyticRemainder d H +
          max (-collisionRate d H)
            (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)))) := by
  set M : ℝ := max (-collisionRate d H)
    (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)) with hM
  set K : ℝ := (actualRowCount d H : ℝ) with hK
  set A : ℝ := (K * H) *
    (d.analyticError + Collision.collisionRemainder (actualRowCount d H) H + M) with hA
  set L : ℝ := Real.log (translationTermCount d.m d.v0 H : ℝ) with hL
  have hKnn : (0 : ℝ) ≤ K := by rw [hK]; exact Nat.cast_nonneg _
  have hexponent : K * H * (d.analyticError + analyticRemainder d H + M) = K * L + A := by
    unfold OAI.PiExponent.LiteralAnalytic.analyticRemainder
    rw [hA, hL]
    field_simp
    ring
  have hstep1 : ‖(actualMinor d H selection).det‖ ≤ (N : ℝ) * Real.exp A := by
    calc ‖(actualMinor d H selection).det‖ = ‖∑ i, terms i‖ := by rw [hexp]
      _ ≤ ∑ i, ‖terms i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin N, Real.exp A := Finset.sum_le_sum fun i _ => hterms i
      _ = (N : ℝ) * Real.exp A := by simp
  have hexp_pos : (0 : ℝ) < Real.exp A := Real.exp_pos A
  calc ‖(actualMinor d H selection).det‖ ≤ (N : ℝ) * Real.exp A := hstep1
    _ ≤ Real.exp (K * L) * Real.exp A := by
        apply mul_le_mul_of_nonneg_right hcount hexp_pos.le
    _ = Real.exp (K * L + A) := by rw [Real.exp_add]
    _ = Real.exp (K * H * (d.analyticError + analyticRemainder d H + M)) := by
        rw [hexponent]
    _ = Real.exp (((actualRowCount d H : ℝ) * H) *
        (d.analyticError + analyticRemainder d H +
          max (-collisionRate d H)
            (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)))) := by
        rw [← hK, ← hM]
