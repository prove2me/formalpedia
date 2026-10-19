-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exists_positive_localized_levelRate_minimizer_of_lsc_and_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/c54eba73-63cd-44e0-99ef-204c595a979c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_eventually_levelRate_zero_le_squared_entropy
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_positive_localized_minimizer_of_lsc_and_smallEntropy

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
open Set Filter Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r : ℕ} {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hκ : ∀ t ∈ Set.Icc (0 : ℝ) s, 0 ≤ levelRate r t)
    (hzero : levelRate r 0 = 0)
    (hupper : ∀ᶠ t : ℝ in 𝓝[>] 0,
      levelRate r t ≤ levelRate 0 t)
    (hlsc : LowerSemicontinuousOn (levelRate r) (Set.Icc (0 : ℝ) s)) :
    ∃ t ∈ Set.Ioc (0 : ℝ) s,
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
          (levelRate r) s =
        levelRate r t +
          MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t := by
  apply exists_positive_localized_minimizer_of_lsc_and_smallEntropy
    hs hs' hκ hzero _ hlsc
  filter_upwards [hupper, eventually_levelRate_zero_le_squared_entropy]
    with t hrt hzero
  exact hrt.trans hzero
end MetricCodes.Spherical.HigherHierarchy
