-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.levelRateSet_zero_nonempty_of_interior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/671f1e9d-61bb-4b7c-85e0-141d9b94a59a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_classicalThreshold_pos
import Theorems.Thm_MetricCodes_Spherical_Gamma_zero
import Theorems.Thm_MetricCodes_Spherical_classicalThreshold_spectral
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Gamma_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_spectralAtom_strictMonoOn

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
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {s : ℝ}
    (hs : 0 < s) (hs' : s < 1) :
    (levelRateSet 0 s).Nonempty := by
  have hthreshold : 0 < MetricCodes.classicalThreshold s :=
    MetricCodes.classicalThreshold_pos hs hs'
  let a : Fin 1 → ℝ := fun _ => MetricCodes.classicalThreshold s + 1
  let b : Fin 0 → ℝ := Fin.elim0
  have ha : Interlacing a b := by
    constructor
    · dsimp [a]
      linarith
    · intro i
      exact Fin.elim0 i
  have hboundary : spectralAtom (MetricCodes.classicalThreshold s) = s / 2 := by
    have h := MetricCodes.Spherical.classicalThreshold_spectral hs hs'
    rw [MetricCodes.Spherical.Gamma_zero hthreshold] at h
    change 2 * spectralAtom (MetricCodes.classicalThreshold s) = s at h
    linarith
  refine ⟨Phi a b, a, b, ha, ?_, rfl⟩
  rw [Gamma_zero]
  have hmono := spectralAtom_strictMonoOn hthreshold.le
    (show 0 ≤ a 0 by dsimp [a]; linarith)
    (show MetricCodes.classicalThreshold s < a 0 by dsimp [a]; linarith)
  linarith
end MetricCodes.Spherical.HigherHierarchy
