-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.rateSet_subset_hierarchyRateSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/a136698c-46c9-44e6-8845-4cbd6207a8af

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_oneRowInterlacing_iff
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Gamma_oneRow
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Phi_oneRow

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
theorem _root_.solution (s : ℝ) :
    MetricCodes.Spherical.rateSet s ⊆ hierarchyRateSet s := by
  rintro z ⟨a, b, ⟨hb, hba, hgap⟩, rfl⟩
  have ha : 0 < a := hb.trans hba
  refine ⟨1, oneRowAmbient a, oneRowStabilizer b,
    oneRowInterlacing_iff.mpr ⟨hb, hba⟩, ?_, ?_⟩
  · simpa [Gamma_oneRow ha] using hgap
  · simp [Phi_oneRow]
end MetricCodes.Spherical.HigherHierarchy
