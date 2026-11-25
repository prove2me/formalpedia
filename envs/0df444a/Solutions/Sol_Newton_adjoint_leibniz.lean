-- Prove2me | solution 1 for Newton.adjoint_leibniz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:17:28.382818+00:00
-- url     : https://prove2.me/submissions/4f3671d2-1b3d-4296-9b0f-1a8c3670b94d

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_StructureConstants
import Theorems.Thm_Newton_adjointAd_zero
import Theorems.Thm_Newton_adjointAd_zero_left
import Theorems.Thm_Newton_adjointAd_self
import Theorems.Thm_Newton_SuNAlgebra_jacobi_identity_alt
import Theorems.Thm_Newton_SuNAlgebra_lie_matrix
attribute [local simp] Newton.SuNAlgebra.lie_matrix


attribute [local simp] Newton.adjointAd.zero
attribute [local simp] Newton.adjointAd.zero_left
attribute [local simp] Newton.adjointAd.self

set_option autoImplicit false
open Matrix
open Newton
variable {N : ℕ}
namespace Newton
theorem _root_.solution (A B C : SuNAlgebra N) :
    adjointAd A ⁅B, C⁆ = ⁅adjointAd A B, C⁆ + ⁅B, adjointAd A C⁆ := by
  simp only [adjointAd]
  exact SuNAlgebra.jacobi_identity_alt A B C
end Newton
