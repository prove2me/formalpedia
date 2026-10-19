-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.localizedLevelRate_zero_eq_classicalLocalizedRate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/10e645c2-0504-47d3-85e0-0b07bafdb57f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_zero_eq_classical

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
    {s : ℝ} (_hs : 0 ≤ s) (hs' : s < 1) :
    localizedLevelRate 0 s = classicalLocalizedRate s := by
  unfold localizedLevelRate classicalLocalizedRate
    MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
  congr 1
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ht, ?_⟩
    change
      MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold t) +
          MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t =
        levelRate 0 t +
          MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t
    rw [levelRate_zero_eq_classical ht.1 (lt_of_le_of_lt ht.2 hs')]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ht, ?_⟩
    change
      levelRate 0 t +
          MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t =
        MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold t) +
          MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t
    rw [levelRate_zero_eq_classical ht.1 (lt_of_le_of_lt ht.2 hs')]
end MetricCodes.Spherical.HigherHierarchy
