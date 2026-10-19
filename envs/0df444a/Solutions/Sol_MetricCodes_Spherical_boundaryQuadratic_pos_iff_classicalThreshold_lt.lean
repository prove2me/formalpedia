-- Prove2me | solution 1 for MetricCodes.Spherical.boundaryQuadratic_pos_iff_classicalThreshold_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/c526a21d-a71b-440c-94b2-d5f638a03dec

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_spectral_iff_quadratic
import Theorems.Thm_MetricCodes_Spherical_zero_fibre_spectral_iff_classicalThreshold_lt

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
    {s a : ℝ} (hs : 0 < s) (hs' : s < 1) (ha : 0 < a) :
    0 < boundaryQuadratic s a ↔ MetricCodes.classicalThreshold s < a := by
  have hzero := spectral_iff_quadratic (s := s) (a := a) (b := 0) ha
  simp only [zero_mul] at hzero
  exact hzero.symm.trans
    (zero_fibre_spectral_iff_classicalThreshold_lt hs hs' ha)
end MetricCodes.Spherical
