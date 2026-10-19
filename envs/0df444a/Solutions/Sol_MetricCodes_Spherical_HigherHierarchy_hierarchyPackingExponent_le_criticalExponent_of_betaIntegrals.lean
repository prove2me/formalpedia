-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.hierarchyPackingExponent_le_criticalExponent_of_betaIntegrals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/2788158c-f1e5-43c3-92fb-5c8c8e9e0fb0

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_hierarchyPackingExponent_le_of_forall
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_hierarchyPackingObjective_le_criticalExponent_of_betaIntegrals

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
theorem _root_.solution
    (hlogMoment :
      (∫ t : ℝ, Real.log t ∂Entropy.comparisonMeasure) = -2)
    (harcsine : ∀ x : ℝ, 0 ≤ x →
      (∫ t : ℝ, t / (t + x) ∂Entropy.arcsineMeasure) =
        1 - Real.sqrt (x / (x + 1 / 4)))
    (hcomparison : ∀ u : ℝ, 0 ≤ u →
      (∫ t : ℝ,
        stieltjesLogAtom (quadraticCoordinate u) t
          ∂Entropy.comparisonMeasure) =
        2 * Real.log 2 * MetricCodes.sphericalEntropy u) :
    hierarchyPackingExponent ≤
      (CohnElkies.criticalBinaryExponent : EReal) := by
  apply hierarchyPackingExponent_le_of_forall
  intro r a b h _
  exact hierarchyPackingObjective_le_criticalExponent_of_betaIntegrals
    h hlogMoment harcsine hcomparison
end MetricCodes.Spherical.HigherHierarchy
