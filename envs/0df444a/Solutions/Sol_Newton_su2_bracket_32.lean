-- Prove2me | solution 1 for Newton.su2_bracket_32
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:17:08.193534+00:00
-- url     : https://prove2.me/submissions/05bc8009-4f80-416f-8279-883e9f9559ed

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
import Theorems.Thm_Newton_su2_bracket_23

set_option autoImplicit false
open Matrix
open Newton
namespace Newton
theorem _root_.solution : ⁅su2Gen3, su2Gen2⁆ = -su2Gen1 := by
  rw [← lie_skew, su2_bracket_23]
end Newton
