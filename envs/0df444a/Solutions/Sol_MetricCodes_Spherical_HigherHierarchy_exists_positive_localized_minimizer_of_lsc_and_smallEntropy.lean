-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exists_positive_localized_minimizer_of_lsc_and_smallEntropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/8f870295-d55e-49d6-9a13-4afcbd6b5061

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_positive_localized_minimizer_of_lowerSemicontinuous
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_sliceCost_continuousOn
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_sliceCost_endpoint_improvement_of_smallEntropy

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
    {κ : ℝ → ℝ} {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hκ : ∀ t ∈ Set.Icc (0 : ℝ) s, 0 ≤ κ t)
    (hzero : κ 0 = 0)
    (hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0,
      κ t ≤ MetricCodes.sphericalEntropy (t ^ 2))
    (hlsc : LowerSemicontinuousOn κ (Set.Icc (0 : ℝ) s)) :
    ∃ t ∈ Set.Ioc (0 : ℝ) s,
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope κ s =
        κ t + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t := by
  exact exists_positive_localized_minimizer_of_lowerSemicontinuous hs.le hs' hκ
    (hlsc.add (sliceCost_continuousOn hs').lowerSemicontinuousOn)
    (exists_sliceCost_endpoint_improvement_of_smallEntropy hs hs' hzero hsmall)
end MetricCodes.Spherical.HigherHierarchy
