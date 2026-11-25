-- Prove2me | solution 1 for Newton.adjointAd_add_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:19:10.957243+00:00
-- url     : https://prove2.me/submissions/f59e5326-24f3-4654-94a5-64f5026cab58

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
    adjointAd (A + B) C = adjointAd A C + adjointAd B C := by
  simp only [adjointAd]
  exact add_lie A B C
end Newton
