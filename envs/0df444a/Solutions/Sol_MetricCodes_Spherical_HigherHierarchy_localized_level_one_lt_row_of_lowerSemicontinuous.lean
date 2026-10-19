-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.localized_level_one_lt_row_of_lowerSemicontinuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/4e7cf004-3b8a-46db-a690-1ee663e33ed6

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_one_lt_variationalRate
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_localizedEnvelope_levelRate_lt_profile_of_positive_minimizer
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_positive_localized_row_minimizer_of_lowerSemicontinuous

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
    MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
        (levelRate 1) s <
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
        MetricCodes.Spherical.variationalRate s := by
  apply localizedEnvelope_levelRate_lt_profile_of_positive_minimizer hs'
    (exists_positive_localized_row_minimizer_of_lowerSemicontinuous
      hs hs' hlsc)
  intro t ht
  exact levelRate_one_lt_variationalRate
    ht.1 (lt_of_le_of_lt ht.2 hs')
end MetricCodes.Spherical.HigherHierarchy
