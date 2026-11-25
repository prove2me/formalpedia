-- Prove2me | solution 1 for Newton.adjointAd.zero_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:39:02.239308+00:00
-- url     : https://prove2.me/submissions/87035d03-9a3b-4bb7-9bb4-b9691ed693c0

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_StructureConstants
import Theorems.Thm_Newton_adjointAd_zero
import Theorems.Thm_Newton_SuNAlgebra_lie_matrix
attribute [local simp] Newton.SuNAlgebra.lie_matrix


attribute [local simp] Newton.adjointAd.zero

set_option autoImplicit false
open Matrix
open Newton
variable {N : ℕ}
open Newton.adjointAd
namespace Newton.adjointAd
theorem _root_.solution (B : SuNAlgebra N) : adjointAd (0 : SuNAlgebra N) B = 0 := by
  simp only [adjointAd]
  exact zero_lie B
end Newton.adjointAd
