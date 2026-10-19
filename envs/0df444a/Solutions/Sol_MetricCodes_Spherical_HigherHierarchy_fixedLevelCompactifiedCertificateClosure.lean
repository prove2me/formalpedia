-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.fixedLevelCompactifiedCertificateClosure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/6eb09a99-f2a8-4a1f-ae00-e48eb09c613c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_fixedLevelCompactifiedCertificateClosure_of_forward_residual
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_fixedLevelForwardCompactifiedResidualLimit

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
theorem _root_.solution
    (r : ℕ) : FixedLevelCompactifiedCertificateClosure r :=
  fixedLevelCompactifiedCertificateClosure_of_forward_residual
    (fixedLevelForwardCompactifiedResidualLimit r)
end MetricCodes.Spherical.HigherHierarchy
