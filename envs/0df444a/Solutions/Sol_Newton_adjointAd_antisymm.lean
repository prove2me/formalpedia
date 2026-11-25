-- Prove2me | solution 1 for Newton.adjointAd.antisymm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:17:24.802932+00:00
-- url     : https://prove2.me/submissions/bf73e5bc-62d7-4c59-8f07-4b3bec102fe5

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
open Newton.adjointAd
namespace Newton.adjointAd
theorem _root_.solution (A B : SuNAlgebra N) : adjointAd A B = -adjointAd B A := by
  simp only [adjointAd]
  rw [← lie_skew]
end Newton.adjointAd
