-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.eventually_rowVariationalRate_le_squared_entropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/ce5ddd7f-51e9-4463-a8a9-a845d525e770

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_variationalRate_lt_classical
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_eventually_levelRate_zero_le_squared_entropy
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_zero_eq_classical

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
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      MetricCodes.Spherical.variationalRate t ≤
        MetricCodes.sphericalEntropy (t ^ 2) := by
  have hupper : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin, hupper,
    eventually_levelRate_zero_le_squared_entropy]
    with t (ht : 0 < t) ht' hzero
  calc
    MetricCodes.Spherical.variationalRate t ≤ levelRate 0 t := by
      rw [levelRate_zero_eq_classical ht.le ht']
      exact (MetricCodes.Spherical.variationalRate_lt_classical ht ht').le
    _ ≤ MetricCodes.sphericalEntropy (t ^ 2) := hzero
end MetricCodes.Spherical.HigherHierarchy
