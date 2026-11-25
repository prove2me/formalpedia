-- Prove2me | solution 1 for Newton.su2_adjointSq_32
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:15:29.411606+00:00
-- url     : https://prove2.me/submissions/5a8375f2-4fbf-402b-9d32-7fcb76fa907a

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
import Theorems.Thm_Newton_su2_bracket_31
import Theorems.Thm_Newton_su2_bracket_32

set_option autoImplicit false
open Matrix
open Newton
namespace Newton
theorem _root_.solution : ⁅su2Gen3, ⁅su2Gen3, su2Gen2⁆⁆ = -su2Gen2 := by
  rw [su2_bracket_32, lie_neg, su2_bracket_31]
end Newton
