-- Prove2me | solution 1 for Newton.su2_adjointSq_12
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:17:49.503738+00:00
-- url     : https://prove2.me/submissions/c6930452-6251-4c12-8f6c-fe28aa14db44

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
import Theorems.Thm_Newton_su2_bracket_12
import Theorems.Thm_Newton_su2_bracket_13

set_option autoImplicit false
open Matrix
open Newton
namespace Newton
theorem _root_.solution : ⁅su2Gen1, ⁅su2Gen1, su2Gen2⁆⁆ = -su2Gen2 := by
  rw [su2_bracket_12, su2_bracket_13]
end Newton
