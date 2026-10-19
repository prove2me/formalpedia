-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Interlacing.Gamma_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/181cffd5-146c-47c3-8ef3-de335091ad7d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_lagrangeWeight_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_spectralAtom_nonneg

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
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchy
namespace MetricCodes.Spherical.HigherHierarchy
namespace Interlacing
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) : 0 ≤ Gamma a b := by
  unfold Gamma
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (h.lagrangeWeight_nonneg i)
      (spectralAtom_nonneg (h.ambient_nonneg i))
end Interlacing
end MetricCodes.Spherical.HigherHierarchy
