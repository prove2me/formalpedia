-- Prove2me | solution 1 for Newton.su2_bracket_21
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:16:58.306208+00:00
-- url     : https://prove2.me/submissions/3491a2cb-8ed0-4bf2-b742-8ef5d22de332

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
import Theorems.Thm_Newton_su2_bracket_12

set_option autoImplicit false
open Matrix
open Newton
namespace Newton
theorem _root_.solution : ⁅su2Gen2, su2Gen1⁆ = -su2Gen3 := by
  rw [← lie_skew, su2_bracket_12]
end Newton
