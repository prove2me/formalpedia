-- Prove2me | solution 1 for MetricCodes.Johnson.zero_fibre_boundary_variance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/243db62d-3acf-433a-8f28-d7386049b6a6

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_spectralLimit_zero_fibre_boundary

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution {δ α u : ℝ}
    (hu : 0 < u) (hua : u < α)
    (ha : α < (1 : ℝ) / 2)
    (hboundary :
      spectralLimit α 0 0 u = asymptoticThreshold δ α) :
    4 * α * (1 - α) =
      (2 * Real.sqrt (u * (1 - u))) ^ 2 +
        2 * δ * (2 * Real.sqrt (u * (1 - u))) + 2 * δ := by
  have hα : 0 < α := lt_trans hu hua
  have hαone : 0 < 1 - α := by linarith
  have huone : 0 < 1 - u := by linarith
  have hA : α * (1 - α) ≠ 0 :=
    (mul_pos hα hαone).ne'
  have hs : 0 ≤ Real.sqrt (u * (1 - u)) :=
    Real.sqrt_nonneg _
  have hplus : 1 + 2 * Real.sqrt (u * (1 - u)) ≠ 0 := by
    nlinarith
  have hrel :
      δ / (2 * α * (1 - α)) =
        (α * (1 - α) - u * (1 - u)) /
          (α * (1 - α) *
            (1 + 2 * Real.sqrt (u * (1 - u)))) := by
    calc
      δ / (2 * α * (1 - α)) =
          1 - spectralLimit α 0 0 u := by
        rw [hboundary]
        unfold asymptoticThreshold
        ring
      _ = _ := spectralLimit_zero_fibre_boundary hu hua ha
  have hsquare := Real.sq_sqrt (mul_pos hu huone).le
  field_simp [hA, hα.ne', hαone.ne', hplus] at hrel
  nlinarith [hsquare]
end MetricCodes.Johnson
