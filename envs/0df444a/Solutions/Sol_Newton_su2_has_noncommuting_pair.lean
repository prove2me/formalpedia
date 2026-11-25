-- Prove2me | solution 1 for Newton.su2_has_noncommuting_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:54:26.408143+00:00
-- url     : https://prove2.me/submissions/50a28be1-0839-4334-a7d8-109549279273

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
import Theorems.Thm_Newton_su2_noncommutative

set_option autoImplicit false
open Matrix
open Newton
namespace Newton
theorem _root_.solution :
    ∃ (A B : SuNAlgebra 2), ⁅A, B⁆ ≠ 0 :=
  ⟨su2Gen1, su2Gen2, su2_noncommutative⟩
end Newton
