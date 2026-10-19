-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.localizedEnvelope_levelRate_succ_lt_of_lowerSemicontinuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/dc93890c-f8fb-4c6e-8d3e-13abea0f34a2

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_nonnegOn_Icc
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_positive_localized_levelRate_minimizer_of_lsc
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
    {r : ℕ} {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hlsc : LowerSemicontinuousOn (levelRate r) (Set.Icc (0 : ℝ) s))
    (hstrict : ∀ t ∈ Set.Ioc (0 : ℝ) s,
      levelRate (r + 1) t < levelRate r t) :
    MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
        (levelRate (r + 1)) s <
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
        (levelRate r) s := by
  exact localizedEnvelope_lt_of_positive_minimizer hs'
    (levelRate_nonnegOn_Icc (r + 1) s)
    (exists_positive_localized_levelRate_minimizer_of_lsc hs hs' hlsc)
    hstrict
end MetricCodes.Spherical.HigherHierarchy
