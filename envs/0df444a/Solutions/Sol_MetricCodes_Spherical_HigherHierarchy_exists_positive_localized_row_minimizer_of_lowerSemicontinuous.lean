-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exists_positive_localized_row_minimizer_of_lowerSemicontinuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/993ea98f-14f2-4bfd-92f0-a3187ee7ac95

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_positive_localized_minimizer_of_lsc_and_smallEntropy
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_rowVariationalRate_nonneg_all
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_rowVariationalRate_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_eventually_rowVariationalRate_le_squared_entropy

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
    {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hlsc : LowerSemicontinuousOn
      MetricCodes.Spherical.variationalRate (Set.Icc (0 : ℝ) s)) :
    ∃ t ∈ Set.Ioc (0 : ℝ) s,
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
          MetricCodes.Spherical.variationalRate s =
        MetricCodes.Spherical.variationalRate t +
          MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t := by
  exact exists_positive_localized_minimizer_of_lsc_and_smallEntropy
    hs hs' (fun t _ => rowVariationalRate_nonneg_all t)
    rowVariationalRate_zero
    eventually_rowVariationalRate_le_squared_entropy hlsc
end MetricCodes.Spherical.HigherHierarchy
