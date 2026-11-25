-- Prove2me | solution 1 for Newton.adjointAd_bracket
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:17:35.695877+00:00
-- url     : https://prove2.me/submissions/c82fd842-a634-44b5-9f27-503f9cdb5ccf

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
theorem _root_.solution (A B C : SuNAlgebra N) :
    adjointAd ⁅A, B⁆ C = adjointAd A (adjointAd B C) - adjointAd B (adjointAd A C) := by
  simp only [adjointAd]
  exact eq_sub_of_add_eq (leibniz_lie A B C).symm
end Newton
