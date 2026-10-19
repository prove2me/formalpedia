-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.fixedLevelCompactifiedCertificateClosure_of_forward_residual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/f7c3fe81-ba8a-4070-b755-ac3b07c5adf4

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_le_compactified_boundary_datum
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_fixedLevelCompactifiedCertificateClosure_of_forward_residual_and_realization

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
    {r : ℕ}
    (hforward : FixedLevelForwardCompactifiedResidualLimit r) :
    FixedLevelCompactifiedCertificateClosure r := by
  apply fixedLevelCompactifiedCertificateClosure_of_forward_residual_and_realization
    hforward
  intro j s c A B hs hs' hc hc' hAB hclosed hlevels
  exact levelRate_le_compactified_boundary_datum
    hs hs' hc hc' A B hAB hclosed hlevels
end MetricCodes.Spherical.HigherHierarchy
