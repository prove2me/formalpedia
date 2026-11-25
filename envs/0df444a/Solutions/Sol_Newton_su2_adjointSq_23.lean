-- Prove2me | solution 1 for Newton.su2_adjointSq_23
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:15:53.247531+00:00
-- url     : https://prove2.me/submissions/0d5d1197-7831-416e-a630-4db9d32665d4

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
import Theorems.Thm_Newton_su2_bracket_23
import Theorems.Thm_Newton_su2_bracket_21

set_option autoImplicit false
open Matrix
open Newton
namespace Newton
theorem _root_.solution : ⁅su2Gen2, ⁅su2Gen2, su2Gen3⁆⁆ = -su2Gen3 := by
  rw [su2_bracket_23, su2_bracket_21]
end Newton
