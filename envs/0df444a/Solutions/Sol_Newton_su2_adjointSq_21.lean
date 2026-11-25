-- Prove2me | solution 1 for Newton.su2_adjointSq_21
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:14:47.777824+00:00
-- url     : https://prove2.me/submissions/86328536-8db1-42c9-9e2d-36fd2a4eb05a

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
import Theorems.Thm_Newton_su2_bracket_23
import Theorems.Thm_Newton_su2_bracket_21

set_option autoImplicit false
open Matrix
open Newton
namespace Newton
theorem _root_.solution : ⁅su2Gen2, ⁅su2Gen2, su2Gen1⁆⁆ = -su2Gen1 := by
  rw [su2_bracket_21, lie_neg, su2_bracket_23]
end Newton
