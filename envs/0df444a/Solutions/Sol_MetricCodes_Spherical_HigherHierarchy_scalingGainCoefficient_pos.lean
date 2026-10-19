-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.scalingGainCoefficient_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/047e0d4b-33c4-41f1-8134-ec9e75ae1d32

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_lagrangeWeight_pos

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
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hlast : 0 < a (Fin.last r)) :
    0 < scalingGainCoefficient a b := by
  unfold scalingGainCoefficient
  apply Finset.sum_pos'
  · intro i _
    have hai : 0 < a i :=
      hlast.trans_le (h.strictAnti_ambient.antitone i.le_last)
    have hquad : 0 < quadraticCoordinate (a i) := by
      unfold quadraticCoordinate
      positivity
    exact (mul_pos (h.lagrangeWeight_pos i) (by positivity)).le
  · refine ⟨0, Finset.mem_univ _, ?_⟩
    have ha : 0 < a 0 :=
      hlast.trans_le (h.strictAnti_ambient.antitone (Fin.zero_le _))
    have hquad : 0 < quadraticCoordinate (a 0) := by
      unfold quadraticCoordinate
      positivity
    exact mul_pos (h.lagrangeWeight_pos 0) (by positivity)
end MetricCodes.Spherical.HigherHierarchy
