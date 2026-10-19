-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.hierarchyPackingObjective_le_criticalExponent_of_betaIntegrals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/a94134b8-7a2a-42a4-8e0b-a0eff96bda38

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_packingObjective_le_limitingPackingExponent_of_logMoment
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_stieltjesPhase_comparison_integrable
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exp_neg_stieltjesPhase_arcsine_integrable
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_stieltjesPhase_arcsine_normalizer
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_stieltjesPhase_comparison_moment

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
    {r : ℕ} {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b)
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
    hierarchyPackingObjective a b ≤ CohnElkies.criticalBinaryExponent := by
  exact Entropy.packingObjective_le_limitingPackingExponent_of_logMoment
    hlogMoment
    (stieltjesPhase_comparison_integrable h hlogMoment)
    (exp_neg_stieltjesPhase_arcsine_integrable h)
    (stieltjesPhase_arcsine_normalizer h harcsine)
    (stieltjesPhase_comparison_moment h hlogMoment hcomparison)
end MetricCodes.Spherical.HigherHierarchy
