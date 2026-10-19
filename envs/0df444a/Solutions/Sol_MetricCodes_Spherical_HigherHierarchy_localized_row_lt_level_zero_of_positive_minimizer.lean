-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.localized_row_lt_level_zero_of_positive_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/2823682e-bcd5-4883-b69b-8a6927e1c9a1

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_variationalRate_lt_classical
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_zero_eq_classical
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_localizedEnvelope_lt_of_positive_minimizer
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_rowVariationalRate_nonneg_all

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
    {s : ℝ} (hs' : s < 1)
    (hmin : ∃ t ∈ Set.Ioc (0 : ℝ) s,
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
          (levelRate 0) s =
        levelRate 0 t +
          MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t) :
    MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
        MetricCodes.Spherical.variationalRate s <
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
        (levelRate 0) s := by
  apply localizedEnvelope_lt_of_positive_minimizer hs'
    (fun t _ => rowVariationalRate_nonneg_all t) hmin
  intro t ht
  rw [levelRate_zero_eq_classical ht.1.le
    (lt_of_le_of_lt ht.2 hs')]
  exact MetricCodes.Spherical.variationalRate_lt_classical
    ht.1 (lt_of_le_of_lt ht.2 hs')
end MetricCodes.Spherical.HigherHierarchy
