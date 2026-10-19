-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.levelRate_one_lt_variationalRate_of_boundary_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/e74a9d21-7bec-46ae-81c0-ba46b55c317d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_classicalThreshold_pos
import Theorems.Thm_MetricCodes_Spherical_boundaryDegree_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_oneRowInterlacing_iff
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Gamma_oneRow
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Phi_oneRow
import Theorems.Thm_MetricCodes_Spherical_boundaryQuadratic_pos_iff_classicalThreshold_lt
import Theorems.Thm_MetricCodes_Spherical_boundaryDegree_lt_longitudinal
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_le
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_sameLevel_opening_strict_refinement
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_boundaryDegree_spectral_eq

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
open scoped Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {s a : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hthreshold : MetricCodes.classicalThreshold s < a)
    (hmin : MetricCodes.Spherical.variationalRate s =
      oneRowBoundaryObjective s a) :
    levelRate 1 s < MetricCodes.Spherical.variationalRate s := by
  have ha : 0 < a :=
    (MetricCodes.classicalThreshold_pos hs hs').trans hthreshold
  have hquadratic :=
    (MetricCodes.Spherical.boundaryQuadratic_pos_iff_classicalThreshold_lt
      hs hs' ha).mpr hthreshold
  let b : ℝ := MetricCodes.Spherical.boundaryDegree s a
  have hb : 0 < b := MetricCodes.Spherical.boundaryDegree_pos hquadratic
  have hba : b < a :=
    MetricCodes.Spherical.boundaryDegree_lt_longitudinal hs ha hquadratic
  have hinterlacing :
      Interlacing (oneRowAmbient a) (oneRowStabilizer b) :=
    oneRowInterlacing_iff.mpr ⟨hb, hba⟩
  have hzero : oneRowAmbient a (Fin.last 1) = 0 := by
    simp [oneRowAmbient]
  obtain ⟨A, _, hA, hgamma, hphi⟩ :=
    exists_sameLevel_opening_strict_refinement
      (by norm_num : 0 < (1 : ℕ)) hinterlacing hzero
  have heq : 2 * Gamma (oneRowAmbient a) (oneRowStabilizer b) = s := by
    rw [Gamma_oneRow ha]
    exact boundaryDegree_spectral_eq ha hquadratic.le
  have hspectral : s < 2 * Gamma A (oneRowStabilizer b) := by
    linarith
  calc
    levelRate 1 s ≤ Phi A (oneRowStabilizer b) :=
      levelRate_le hA hspectral
    _ < Phi (oneRowAmbient a) (oneRowStabilizer b) := hphi
    _ = oneRowBoundaryObjective s a := by
      rw [Phi_oneRow]
      rfl
    _ = MetricCodes.Spherical.variationalRate s := hmin.symm
end MetricCodes.Spherical.HigherHierarchy
