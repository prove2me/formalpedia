-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.spectralAtom_strictMonoOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/874b284c-e891-4a55-abee-37e0030ed7ff

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_spectralAtom_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_spectralAtom_sq

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
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution :
    StrictMonoOn spectralAtom (Set.Ici (0 : ℝ)) := by
  intro u hu v hv huv
  change 0 ≤ u at hu
  change 0 ≤ v at hv
  have hquad := quadraticCoordinate_strictMonoOn hu hv huv
  have hqu : 0 ≤ quadraticCoordinate u := by
    unfold quadraticCoordinate
    positivity
  have hqv : 0 ≤ quadraticCoordinate v := by
    unfold quadraticCoordinate
    positivity
  have hdenu : 0 < 1 + 4 * quadraticCoordinate u := by positivity
  have hdenv : 0 < 1 + 4 * quadraticCoordinate v := by positivity
  have hsquare : spectralAtom u ^ 2 < spectralAtom v ^ 2 := by
    rw [spectralAtom_sq hu, spectralAtom_sq hv]
    apply (div_lt_div_iff₀ hdenu hdenv).mpr
    nlinarith
  have hnonneg := spectralAtom_nonneg hu
  have hnonneg' := spectralAtom_nonneg hv
  nlinarith
end MetricCodes.Spherical.HigherHierarchy
