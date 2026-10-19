-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.comparisonLogAtom_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/912ee103-e258-47d3-8eed-32f07e5d741d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_comparison_logAtom_integral
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_sphericalEntropy_naturalLogIdentity

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {u : ℝ} (hu : 0 ≤ u) :
    (∫ t : ℝ,
      stieltjesLogAtom (quadraticCoordinate u) t
        ∂Entropy.comparisonMeasure) =
      2 * Real.log 2 * MetricCodes.sphericalEntropy u := by
  change (∫ t : ℝ,
    Real.log ((t + u * (1 + u)) / t)
      ∂Entropy.comparisonMeasure) = _
  rw [Entropy.comparison_logAtom_integral hu]
  exact sphericalEntropy_naturalLogIdentity u
end MetricCodes.Spherical.HigherHierarchy
