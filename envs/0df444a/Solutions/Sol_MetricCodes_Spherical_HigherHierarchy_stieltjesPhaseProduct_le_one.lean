-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.stieltjesPhaseProduct_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/2eaf852e-52d1-4e98-ab7b-f6d9234c5db0

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exp_neg_stieltjesPhase_eq_product
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_stieltjesPhase_nonneg

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
    stieltjesPhaseProduct a b t ≤ 1 := by
  rw [← exp_neg_stieltjesPhase_eq_product h ht]
  exact (Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (stieltjesPhase_nonneg h ht)))
end MetricCodes.Spherical.HigherHierarchy
