-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.log_inv_lt_half_inv_sub_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/30ebcb9c-4593-4dd8-aa24-d192097d6d15

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Numerics_log_ratio_upper

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
    Real.log (1 / t) < (1 / t - t) / 2 := by
  let x : ℝ := (1 - t) / (1 + t)
  have hx : 0 < x := by dsimp [x]; positivity
  have hx' : x < 1 := by
    dsimp [x]
    exact (div_lt_one (by linarith)).mpr (by linarith)
  have hden : 0 < 1 - x ^ 2 := by nlinarith
  have hratio : (1 + x) / (1 - x) = 1 / t := by
    dsimp [x]
    field_simp [ht.ne']
    ring
  have hseries :
      Real.log (1 / t) ≤ MetricCodes.Numerics.logSeriesUpper x 2 := by
    rw [← hratio]
    exact MetricCodes.Numerics.log_ratio_upper hx.le hx' 2
  have hstrict :
      MetricCodes.Numerics.logSeriesUpper x 2 <
        2 * x / (1 - x ^ 2) := by
    have hgap : 2 * x / (1 - x ^ 2) -
        MetricCodes.Numerics.logSeriesUpper x 2 =
          (4 / 3 : ℝ) * x ^ 3 := by
      unfold MetricCodes.Numerics.logSeriesUpper
        MetricCodes.Numerics.logSeriesLower
      norm_num [Finset.sum_range_succ]
      field_simp [hden.ne']
      ring
    exact sub_pos.mp (by rw [hgap]; positivity)
  have hvalue : 2 * x / (1 - x ^ 2) = (1 / t - t) / 2 := by
    dsimp [x]
    field_simp [ht.ne']
    rw [show (1 + t) ^ 2 - (1 - t) ^ 2 = 4 * t by ring]
    field_simp [ht.ne']
    ring
  exact hseries.trans_lt (hstrict.trans_eq hvalue)
end MetricCodes.Spherical.HigherHierarchy
