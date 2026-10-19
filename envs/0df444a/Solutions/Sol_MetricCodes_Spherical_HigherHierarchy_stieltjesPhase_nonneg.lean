-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.stieltjesPhase_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/60396e9d-ad1f-4b46-b6f8-e5031c6a5934

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_ambient_quadratic_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_stabilizer_quadratic_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_stieltjesPhase_eq_log_sum
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_quadratic_phase_interval

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
open MeasureTheory
open scoped BigOperators Interval
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {t : ℝ} (ht : 0 < t) :
    0 ≤ stieltjesPhase a b t := by
  rw [stieltjesPhase_eq_log_sum h ht]
  apply add_nonneg
  · apply Real.log_nonneg
    apply (le_div_iff₀ ht).2
    simpa using h.ambient_quadratic_nonneg (Fin.last r)
  · apply Finset.sum_nonneg
    intro i _
    apply Real.log_nonneg
    apply (le_div_iff₀ (by linarith [h.stabilizer_quadratic_pos i])).2
    nlinarith [h.quadratic_phase_interval i]
end MetricCodes.Spherical.HigherHierarchy
