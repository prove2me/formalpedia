-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyBoxSpectral.constantRayleigh_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/62ecb86f-ccec-48ac-a0f6-e3ae5e671999

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyBoxSpectral_boxVertex_card
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyBoxSpectral_constantRayleigh_eq
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyBoxSpectral_forwardFace_sum

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
    (weight : Fin (r + 1) → ℝ) :
    constantRayleigh (fun _ : BoxVertex r m => weight) =
      (2 * (m : ℝ) / (m + 1 : ℝ)) *
        ∑ i : Fin (r + 1), weight i := by
  rw [constantRayleigh_eq, boxVertex_card]
  rw [Finset.sum_comm]
  simp_rw [forwardFace_sum]
  rw [← Finset.mul_sum]
  push_cast
  have hbase : (m : ℝ) + 1 ≠ 0 := by positivity
  have hpower : ((m : ℝ) + 1) ^ r ≠ 0 :=
    pow_ne_zero _ hbase
  rw [pow_succ]
  field_simp
end MetricCodes.Spherical.HigherHierarchyBoxSpectral
