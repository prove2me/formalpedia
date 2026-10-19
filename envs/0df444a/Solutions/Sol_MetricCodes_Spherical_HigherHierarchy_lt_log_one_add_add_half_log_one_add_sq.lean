-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.lt_log_one_add_add_half_log_one_add_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/e4783c21-6eff-4794-bd5c-863cecee43f1

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Numerics_log_ratio_lower

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {t : ℝ}
    (ht : 0 < t) (ht' : t < 1) :
    t < Real.log (1 + t) + (1 / 2 : ℝ) * Real.log (1 + t ^ 2) := by
  let x : ℝ := t / (2 + t)
  let y : ℝ := t ^ 2 / (2 + t ^ 2)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hx' : x < 1 := by
    dsimp [x]
    exact (div_lt_one (by linarith)).mpr (by linarith)
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hy' : y < 1 := by
    dsimp [y]
    exact (div_lt_one (by positivity)).mpr (by linarith)
  have hxratio : (1 + x) / (1 - x) = 1 + t := by
    dsimp [x]
    field_simp
    ring
  have hyratio : (1 + y) / (1 - y) = 1 + t ^ 2 := by
    dsimp [y]
    field_simp
    ring
  have hxlog : 2 * x ≤ Real.log (1 + t) := by
    have h := MetricCodes.Numerics.log_ratio_lower hx hx' 1
    rw [hxratio] at h
    simpa [MetricCodes.Numerics.logSeriesLower,
      Finset.sum_range_succ] using h
  have hylog : 2 * y ≤ Real.log (1 + t ^ 2) := by
    have h := MetricCodes.Numerics.log_ratio_lower hy hy' 1
    rw [hyratio] at h
    simpa [MetricCodes.Numerics.logSeriesLower,
      Finset.sum_range_succ] using h
  have hrational : t < 2 * x + y := by
    dsimp [x, y]
    have hden₁ : 0 < 2 + t := by linarith
    have hden₂ : 0 < 2 + t ^ 2 := by positivity
    apply sub_pos.mp
    have hidentity :
        2 * (t / (2 + t)) + t ^ 2 / (2 + t ^ 2) - t =
          t ^ 3 * (1 - t) / ((2 + t) * (2 + t ^ 2)) := by
      field_simp
      ring
    rw [hidentity]
    exact div_pos
      (mul_pos (pow_pos ht 3) (sub_pos.mpr ht'))
      (mul_pos hden₁ hden₂)
  nlinarith
end MetricCodes.Spherical.HigherHierarchy
