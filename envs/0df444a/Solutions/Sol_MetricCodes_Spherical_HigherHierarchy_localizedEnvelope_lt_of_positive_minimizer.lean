-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.localizedEnvelope_lt_of_positive_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/f408eba8-f86f-456c-b6d2-4052f2ef70b2

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_localizedEnvelope_lt_of_minimizer

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
    {κ κ' : ℝ → ℝ} {s : ℝ}
    (hs' : s < 1)
    (hκ' : ∀ t ∈ Set.Icc (0 : ℝ) s, 0 ≤ κ' t)
    (hmin : ∃ t ∈ Set.Ioc (0 : ℝ) s,
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope κ s =
        κ t + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t)
    (hstrict : ∀ t ∈ Set.Ioc (0 : ℝ) s, κ' t < κ t) :
    MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope κ' s <
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope κ s := by
  obtain ⟨t, ht, hmin⟩ := hmin
  exact localizedEnvelope_lt_of_minimizer hs'
    ⟨ht.1.le, ht.2⟩ hκ' hmin (hstrict t ht)
end MetricCodes.Spherical.HigherHierarchy
