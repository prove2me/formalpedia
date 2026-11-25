-- Prove2me | solution 1 for Newton.adjointAd2_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:19:32.635808+00:00
-- url     : https://prove2.me/submissions/ed367d3a-1c5c-44e8-adf7-b02912e34130

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_StructureConstants

set_option autoImplicit false
open Matrix
open Newton
variable {N : ℕ}
namespace Newton
theorem _root_.solution (A B : SuNAlgebra N) :
    adjointAd2 A B = ⁅A, ⁅A, B⁆⁆ := rfl
end Newton
