-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Phi_opening_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/6461fa7e-fee9-4f5e-887c-9d742bf51f20

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_zero_ne_last_of_level_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_sum_sphericalEntropy_update

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
    (hr : 0 < r)
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (hzero : a (Fin.last r) = 0) (η t : ℝ) :
    Phi (openingAmbient a (η * t) (t ^ 2)) b - Phi a b =
      MetricCodes.sphericalEntropy (a 0 - η * t) -
        MetricCodes.sphericalEntropy (a 0) +
        MetricCodes.sphericalEntropy (t ^ 2) := by
  have hne := zero_ne_last_of_level_pos hr
  unfold Phi openingAmbient
  rw [sum_sphericalEntropy_update, sum_sphericalEntropy_update]
  have hlast :
      Function.update a 0 (a 0 - η * t) (Fin.last r) = 0 := by
    simp [Ne.symm hne, hzero]
  rw [hlast]
  simp [MetricCodes.sphericalEntropy]
  ring
end MetricCodes.Spherical.HigherHierarchy
