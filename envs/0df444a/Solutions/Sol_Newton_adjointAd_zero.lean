-- Prove2me | solution 1 for Newton.adjointAd.zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:35:02.953018+00:00
-- url     : https://prove2.me/submissions/dcff1a60-ff0a-444e-8033-1a84f304ad83

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
theorem _root_.solution (A : SuNAlgebra N) : adjointAd A (0 : SuNAlgebra N) = 0 := by
  simp only [adjointAd]
  exact lie_zero A
end Newton.adjointAd
