-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exists_positive_localized_levelRate_minimizer_of_lsc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/e88d4267-f89d-484f-acb8-c7fde47f430b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_le_levelRate_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_nonnegOn_Icc
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_positive_localized_levelRate_minimizer_of_lsc_and_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_at_zero

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
    (hlsc : LowerSemicontinuousOn (levelRate r) (Set.Icc (0 : ℝ) s)) :
    ∃ t ∈ Set.Ioc (0 : ℝ) s,
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
          (levelRate r) s =
        levelRate r t +
          MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t := by
  apply exists_positive_localized_levelRate_minimizer_of_lsc_and_zero
    hs hs' (levelRate_nonnegOn_Icc r s) (levelRate_at_zero r) _ hlsc
  have hupper : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin, hupper] with t (ht : 0 < t) ht'
  exact levelRate_le_levelRate_zero ht ht'
end MetricCodes.Spherical.HigherHierarchy
