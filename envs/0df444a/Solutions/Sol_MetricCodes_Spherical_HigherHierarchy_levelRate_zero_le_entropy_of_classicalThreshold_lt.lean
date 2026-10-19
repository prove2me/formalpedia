-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.levelRate_zero_le_entropy_of_classicalThreshold_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/599a1adb-96b1-4a03-8ecb-ce4453113afa

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_classicalThreshold_pos
import Theorems.Thm_MetricCodes_Spherical_Gamma_zero
import Theorems.Thm_MetricCodes_Spherical_classicalThreshold_spectral
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Gamma_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Phi_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_spectralAtom_strictMonoOn
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_le

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
    (ha : MetricCodes.classicalThreshold s < a) :
    levelRate 0 s ≤ MetricCodes.sphericalEntropy a := by
  have hthreshold := MetricCodes.classicalThreshold_pos hs hs'
  let A : Fin 1 → ℝ := fun _ => a
  let B : Fin 0 → ℝ := Fin.elim0
  have hA : Interlacing A B := by
    constructor
    · dsimp [A]
      linarith
    · intro i
      exact Fin.elim0 i
  have hboundary : spectralAtom (MetricCodes.classicalThreshold s) = s / 2 := by
    have h := MetricCodes.Spherical.classicalThreshold_spectral hs hs'
    rw [MetricCodes.Spherical.Gamma_zero hthreshold] at h
    change 2 * spectralAtom (MetricCodes.classicalThreshold s) = s at h
    linarith
  have hmono := spectralAtom_strictMonoOn hthreshold.le
    (show 0 ≤ a by linarith) ha
  have hgap : s < 2 * Gamma A B := by
    rw [Gamma_zero]
    change s < 2 * spectralAtom a
    linarith
  simpa [Phi_zero, A] using levelRate_le hA hgap
end MetricCodes.Spherical.HigherHierarchy
