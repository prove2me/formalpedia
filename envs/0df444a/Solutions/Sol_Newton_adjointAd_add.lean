-- Prove2me | solution 1 for Newton.adjointAd.add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:17:07.862937+00:00
-- url     : https://prove2.me/submissions/e4b23d3d-ca3b-4480-b725-1fe210ad1986

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_StructureConstants
import Theorems.Thm_Newton_SuNAlgebra_lie_matrix
attribute [local simp] Newton.SuNAlgebra.lie_matrix



set_option autoImplicit false
open Matrix
open Newton
variable {N : ℕ}
open Newton.adjointAd
namespace Newton.adjointAd
theorem _root_.solution (A B C : SuNAlgebra N) :
    adjointAd A (B + C) = adjointAd A B + adjointAd A C := by
  simp only [adjointAd]
  exact lie_add A B C
end Newton.adjointAd
