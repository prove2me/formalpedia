-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.genuineCompactifiedHierarchyTransfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/a1999f5e-2d62-4fd1-b625-d63b97971920

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_Gamma_prepend_scale
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_hierarchyVariationalRate_le_compactified_certificate_of_spectral_limit

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
set_option autoImplicit false
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution :
    GenuineCompactifiedHierarchyTransfer := by
  intro r s c hc hc' a b h hscaled
  exact hierarchyVariationalRate_le_compactified_certificate_of_spectral_limit
    hc hc' a b h hscaled (tendsto_Gamma_prepend_scale h hc hc')
end MetricCodes.Spherical.HigherHierarchy
