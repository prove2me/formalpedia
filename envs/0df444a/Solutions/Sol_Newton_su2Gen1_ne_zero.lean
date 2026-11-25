-- Prove2me | solution 1 for Newton.su2Gen1_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:13:13.017264+00:00
-- url     : https://prove2.me/submissions/73ae9548-20f6-4695-aecd-d1da1f41efe2

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
import Theorems.Thm_Newton_su2_noncommutative
import Theorems.Thm_Newton_SuNAlgebra_lie_matrix
attribute [local simp] Newton.SuNAlgebra.lie_matrix



set_option autoImplicit false
open Matrix
open Newton
namespace Newton
theorem _root_.solution : su2Gen1 ≠ 0 := by
  intro h
  have := su2_noncommutative
  rw [h] at this
  simp only [zero_lie, ne_eq, not_true_eq_false] at this
end Newton
