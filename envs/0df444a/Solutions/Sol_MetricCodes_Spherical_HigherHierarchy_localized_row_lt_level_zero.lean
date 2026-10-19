-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.localized_row_lt_level_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/53e30490-a8a6-443d-8c8e-3ca7205869c7

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_positive_localized_classical_minimizer
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_localized_row_lt_level_zero_of_positive_minimizer

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
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
        MetricCodes.Spherical.variationalRate s <
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
        (levelRate 0) s :=
  localized_row_lt_level_zero_of_positive_minimizer hs'
    (exists_positive_localized_classical_minimizer hs hs')
end MetricCodes.Spherical.HigherHierarchy
