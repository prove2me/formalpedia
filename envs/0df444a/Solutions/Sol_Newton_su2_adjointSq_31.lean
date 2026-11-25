-- Prove2me | solution 1 for Newton.su2_adjointSq_31
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:15:11.549391+00:00
-- url     : https://prove2.me/submissions/467024e9-07a0-46e4-9390-bc277249ebad

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
import Theorems.Thm_Newton_su2_bracket_31
import Theorems.Thm_Newton_su2_bracket_32

set_option autoImplicit false
open Matrix
open Newton
namespace Newton
theorem _root_.solution : ⁅su2Gen3, ⁅su2Gen3, su2Gen1⁆⁆ = -su2Gen1 := by
  rw [su2_bracket_31, su2_bracket_32]
end Newton
