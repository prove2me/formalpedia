-- Prove2me | solution 1 for MetricCodes.Spherical.feasible_iff_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/fc99f280-b1dd-470a-8cf5-09d1aa335e6f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_classicalThreshold_pos
import Theorems.Thm_MetricCodes_Spherical_spectral_iff_quadratic
import Theorems.Thm_MetricCodes_Spherical_quadratic_iff_boundaryDegree
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
    {s a b : ℝ} (hs : 0 < s) (hs' : s < 1) :
    Feasible s a b ↔
      MetricCodes.classicalThreshold s < a ∧
        0 < b ∧ b < boundaryDegree s a := by
  constructor
  · rintro ⟨hb, hba, hspectral⟩
    have ha : 0 < a := hb.trans hba
    have hquadratic : 0 < boundaryQuadratic s a := by
      have hstrict := (spectral_iff_quadratic ha).mp hspectral
      nlinarith [mul_pos hb (by linarith : 0 < 1 + b)]
    exact ⟨(boundaryQuadratic_pos_iff_classicalThreshold_lt
      hs hs' ha).mp hquadratic, hb,
      (quadratic_iff_boundaryDegree hb.le hquadratic).mp
        ((spectral_iff_quadratic ha).mp hspectral)⟩
  · rintro ⟨hthreshold, hb, hboundary⟩
    have hthreshold_pos := MetricCodes.classicalThreshold_pos hs hs'
    have ha : 0 < a := hthreshold_pos.trans hthreshold
    have hquadratic :=
      (boundaryQuadratic_pos_iff_classicalThreshold_lt
        hs hs' ha).mpr hthreshold
    have hba : b < a := hboundary.trans
      (boundaryDegree_lt_longitudinal hs ha hquadratic)
    refine ⟨hb, hba, (spectral_iff_quadratic ha).mpr ?_⟩
    exact (quadratic_iff_boundaryDegree hb.le hquadratic).mpr
      hboundary
end MetricCodes.Spherical
