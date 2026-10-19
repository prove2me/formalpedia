-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.eventually_squared_spectralCertificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/3984cb01-fcf4-4f5b-9d90-76fbd49a2564

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_spectralAtom_sq_div

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
open Set Filter Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution :
    ∀ᶠ t : ℝ in 𝓝[>] 0, t < 2 * spectralAtom (t ^ 2) := by
  have hratio :
      ∀ᶠ t : ℝ in 𝓝[>] 0,
        (1 / 2 : ℝ) < spectralAtom (t ^ 2) / t :=
    tendsto_spectralAtom_sq_div.eventually
      (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [hratio, self_mem_nhdsWithin] with t hratio (ht : 0 < t)
  have hmul := (lt_div_iff₀ ht).mp hratio
  linarith
end MetricCodes.Spherical.HigherHierarchy
