-- Prove2me | solution 1 for GlobalTheory.DiscUniformisation.E_cube_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:15.493917+00:00
-- url     : https://prove2.me/submissions/5da4b7a1-d118-48ec-8ab0-a67d30a162f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TendstoCoeffZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm MatrixGroups EisensteinSeries Filter Topology
open GlobalTheory GlobalTheory.DiscUniformisation
namespace GlobalTheory.DiscUniformisation
theorem _root_.solution (z : ℍ) : E₄ z ^ 3 ≠ E₆ z ^ 2 := by
  intro h
  apply ModularForm.discriminant_ne_zero z
  rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq, h, sub_self, zero_div]
end GlobalTheory.DiscUniformisation
