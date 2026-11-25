-- Prove2me | solution 1 for Newton.su2_noncommutative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:19:04.645955+00:00
-- url     : https://prove2.me/submissions/772add6e-657a-44df-8582-89cf3d398b6d

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
import Theorems.Thm_Newton_su2_bracket_12
import Theorems.Thm_Newton_su2Gen3_ne_zero

set_option autoImplicit false
open Matrix
open Newton
namespace Newton
theorem _root_.solution : ⁅su2Gen1, su2Gen2⁆ ≠ 0 := by
  rw [su2_bracket_12]
  exact su2Gen3_ne_zero
end Newton
