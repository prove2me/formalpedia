-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.hierarchyPackingExponent_le_criticalExponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/92ad5aab-818a-4263-8527-d8a9a929f67a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_comparison_logMoment
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_comparisonLogAtom_moment
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_hierarchyPackingExponent_le_criticalExponent_of_betaIntegrals
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_arcsineMeasure_stieltjesKernel

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
theorem _root_.solution :
    hierarchyPackingExponent ≤
      (CohnElkies.criticalBinaryExponent : EReal) :=
  hierarchyPackingExponent_le_criticalExponent_of_betaIntegrals
    Entropy.comparison_logMoment
    (fun _ hx => arcsineMeasure_stieltjesKernel hx)
    (fun _ hu => comparisonLogAtom_moment hu)
end MetricCodes.Spherical.HigherHierarchy
