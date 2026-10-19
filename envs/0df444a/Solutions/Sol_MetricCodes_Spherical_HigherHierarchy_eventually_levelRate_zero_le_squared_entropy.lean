-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.eventually_levelRate_zero_le_squared_entropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/4726bdbe-60fd-4662-b066-a3b426ee2958

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_zero_le_squared_entropy_of_spectral
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_eventually_squared_spectralCertificate

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
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      levelRate 0 t ≤ MetricCodes.sphericalEntropy (t ^ 2) := by
  filter_upwards [eventually_squared_spectralCertificate,
    self_mem_nhdsWithin] with t hspec (ht : 0 < t)
  exact levelRate_zero_le_squared_entropy_of_spectral ht hspec
end MetricCodes.Spherical.HigherHierarchy
