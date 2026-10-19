-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.compensatedPhiPath_differentiableAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/74caac62-5015-4291-a511-ee94755633f5

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_hasDerivAt_sphericalEntropy
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_scaleCoordinate_compensated_differentiableAt_zero

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
    DifferentiableAt ℝ (compensatedPhiPath a b) 0 := by
  unfold compensatedPhiPath Phi scaleAmbient scaleStabilizer
  apply DifferentiableAt.sub
  · apply DifferentiableAt.fun_sum
    intro i _
    have hai : 0 < a i :=
      hlast.trans_le (h.strictAnti_ambient.antitone i.le_last)
    have hinner := scaleCoordinate_compensated_differentiableAt_zero
      a b hai.le
    have hvalue :
        scaleCoordinate (compensatedScalingFactor a b 0) (a i) = a i := by
      rw [compensatedScalingFactor_zero, scaleCoordinate_one hai.le]
    have houter : DifferentiableAt ℝ MetricCodes.sphericalEntropy
        (scaleCoordinate (compensatedScalingFactor a b 0) (a i)) := by
      rw [hvalue]
      exact (MetricCodes.Spherical.hasDerivAt_sphericalEntropy hai).differentiableAt
    simpa [Function.comp_def] using houter.comp 0 hinner
  · apply DifferentiableAt.fun_sum
    intro i _
    have hbi := h.stabilizer_pos i
    have hinner := scaleCoordinate_compensated_differentiableAt_zero
      a b hbi.le
    have hvalue :
        scaleCoordinate (compensatedScalingFactor a b 0) (b i) = b i := by
      rw [compensatedScalingFactor_zero, scaleCoordinate_one hbi.le]
    have houter : DifferentiableAt ℝ MetricCodes.sphericalEntropy
        (scaleCoordinate (compensatedScalingFactor a b 0) (b i)) := by
      rw [hvalue]
      exact (MetricCodes.Spherical.hasDerivAt_sphericalEntropy hbi).differentiableAt
    simpa [Function.comp_def] using houter.comp 0 hinner
end MetricCodes.Spherical.HigherHierarchy
