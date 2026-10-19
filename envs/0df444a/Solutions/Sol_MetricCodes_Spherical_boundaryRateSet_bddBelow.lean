-- Prove2me | solution 1 for MetricCodes.Spherical.boundaryRateSet_bddBelow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/bfc6c4f3-163f-4d4c-b7e8-72aee5aff07f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_classicalThreshold_pos
import Theorems.Thm_MetricCodes_Spherical_sphericalEntropy_sub_nonneg
import Theorems.Thm_MetricCodes_Spherical_boundaryDegree_pos
import Theorems.Thm_MetricCodes_Spherical_boundaryQuadratic_pos_iff_classicalThreshold_lt
import Theorems.Thm_MetricCodes_Spherical_boundaryDegree_lt_longitudinal

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
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical
theorem _root_.solution
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    BddBelow (boundaryRateSet s) := by
  refine ⟨0, ?_⟩
  rintro r ⟨a, hthreshold, rfl⟩
  have ha := (MetricCodes.classicalThreshold_pos hs hs').trans hthreshold
  have hquadratic :=
    (boundaryQuadratic_pos_iff_classicalThreshold_lt
      hs hs' ha).mpr hthreshold
  exact sphericalEntropy_sub_nonneg
    (boundaryDegree_pos hquadratic).le
    (boundaryDegree_lt_longitudinal hs ha hquadratic).le
end MetricCodes.Spherical
