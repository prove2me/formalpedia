-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.localizedEnvelope_levelRate_lt_profile_of_positive_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/1159db7c-9a32-4d86-9e35-f8c7df7b2f55

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_nonnegOn_Icc
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_localizedEnvelope_lt_of_positive_minimizer

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
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r : ℕ} {κ : ℝ → ℝ} {s : ℝ}
    (hs' : s < 1)
    (hmin : ∃ t ∈ Set.Ioc (0 : ℝ) s,
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope κ s =
        κ t + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t)
    (hstrict : ∀ t ∈ Set.Ioc (0 : ℝ) s, levelRate r t < κ t) :
    MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
        (levelRate r) s <
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope κ s := by
  exact localizedEnvelope_lt_of_positive_minimizer hs'
    (levelRate_nonnegOn_Icc r s) hmin hstrict
end MetricCodes.Spherical.HigherHierarchy
