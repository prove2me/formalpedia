-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.levelRate_zero_le_squared_entropy_of_spectral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/0ab759ea-924a-4f41-b251-8501db80dcd9

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_Gamma_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Gamma_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Phi_zero
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
open Set Filter Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {t : ℝ}
    (ht : 0 < t) (hspectral : t < 2 * spectralAtom (t ^ 2)) :
    levelRate 0 t ≤ MetricCodes.sphericalEntropy (t ^ 2) := by
  let a : Fin 1 → ℝ := fun _ => t ^ 2
  let b : Fin 0 → ℝ := Fin.elim0
  have ha : Interlacing a b := by
    constructor
    · dsimp [a]
      positivity
    · intro i
      exact Fin.elim0 i
  calc
    levelRate 0 t ≤ Phi a b :=
      levelRate_le ha (by simpa [Gamma_zero, a] using hspectral)
    _ = MetricCodes.sphericalEntropy (t ^ 2) := by
      simp [Phi_zero, a]
end MetricCodes.Spherical.HigherHierarchy
