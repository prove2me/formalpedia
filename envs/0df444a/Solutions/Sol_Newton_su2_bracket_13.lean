-- Prove2me | solution 1 for Newton.su2_bracket_13
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:17:18.154011+00:00
-- url     : https://prove2.me/submissions/a8a42ebf-3bba-47b9-a8ce-723d94eba820

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
import Theorems.Thm_Newton_su2_bracket_31

set_option autoImplicit false
open Matrix
open Newton
namespace Newton
theorem _root_.solution : ⁅su2Gen1, su2Gen3⁆ = -su2Gen2 := by
  rw [← lie_skew, su2_bracket_31]
end Newton
