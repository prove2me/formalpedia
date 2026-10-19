-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyBoxSpectral.forwardFace_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/1120ae83-1772-444a-a81b-1b8e266db97e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyBoxSpectral_forwardFace_card

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
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Matrix Topology
open MetricCodes.Spherical.HigherHierarchyBoxSpectral
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherHierarchyBoxSpectral
theorem _root_.solution {r m : ℕ}
    (i : Fin (r + 1)) (c : ℝ) :
    (∑ v : BoxVertex r m,
      if (v i).val < m then c else 0) =
        (m : ℝ) * ((m + 1 : ℕ) : ℝ) ^ r * c := by
  classical
  have hterm (v : BoxVertex r m) :
      (if (v i).val < m then c else 0) =
        (if (v i).val < m then (1 : ℝ) else 0) * c := by
    split_ifs <;> simp
  simp_rw [hterm, ← Finset.sum_mul]
  rw [Finset.sum_boole]
  rw [forwardFace_card]
  norm_cast
end MetricCodes.Spherical.HigherHierarchyBoxSpectral
