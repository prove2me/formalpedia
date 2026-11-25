-- Prove2me | solution 1 for Newton.adjointAd2_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:19:53.983662+00:00
-- url     : https://prove2.me/submissions/8aba1475-7ff0-418f-9e3e-5f9031ce3c87

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_StructureConstants
import Theorems.Thm_Newton_adjointAd_zero
import Theorems.Thm_Newton_adjointAd_zero_left
import Theorems.Thm_Newton_adjointAd_self
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
theorem _root_.solution (A : SuNAlgebra N) : adjointAd2 A A = 0 := by
  simp only [adjointAd2, adjointAd]
  rw [lie_self]
  exact lie_zero A
end Newton
