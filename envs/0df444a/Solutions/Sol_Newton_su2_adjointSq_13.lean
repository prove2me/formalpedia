-- Prove2me | solution 1 for Newton.su2_adjointSq_13
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:19:45.134144+00:00
-- url     : https://prove2.me/submissions/6effe719-2d95-4674-92ba-6c3d74c0b9d1

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
import Theorems.Thm_Newton_su2_bracket_12
import Theorems.Thm_Newton_su2_bracket_13

set_option autoImplicit false
open Matrix
open Newton
namespace Newton
theorem _root_.solution : ⁅su2Gen1, ⁅su2Gen1, su2Gen3⁆⁆ = -su2Gen3 := by
  rw [su2_bracket_13, lie_neg, su2_bracket_12]
end Newton
