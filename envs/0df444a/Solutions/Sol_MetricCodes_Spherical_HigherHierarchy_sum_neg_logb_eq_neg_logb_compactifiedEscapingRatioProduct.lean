-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.sum_neg_logb_eq_neg_logb_compactifiedEscapingRatioProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/66aa345d-df23-4582-a2fb-e5f3fe1c36ac

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
open scoped BigOperators
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r k j : ℕ} (hkj : k + j = r) (d : Fin r → ℝ)
    (hd : ∀ i : Fin r, i.val < k → 0 < d i) :
    (∑ i : Fin k, -Real.logb 2 (d ⟨i.val, by omega⟩)) =
      -Real.logb 2 (compactifiedEscapingRatioProduct hkj d) := by
  rw [Finset.sum_neg_distrib, compactifiedEscapingRatioProduct,
    Real.logb_prod]
  intro i _
  exact (hd ⟨i.val, by omega⟩ i.isLt).ne'
end MetricCodes.Spherical.HigherHierarchy
