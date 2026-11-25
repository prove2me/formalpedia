-- Prove2me | solution 1 for Newton.su2Gen2_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:14:39.576973+00:00
-- url     : https://prove2.me/submissions/1a81abf3-9311-46e7-a78e-4f9792cb0050

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
import Theorems.Thm_Newton_su2_bracket_12
import Theorems.Thm_Newton_su2Gen3_ne_zero
import Theorems.Thm_Newton_SuNAlgebra_lie_matrix
attribute [local simp] Newton.SuNAlgebra.lie_matrix



set_option autoImplicit false
open Matrix
open Newton
namespace Newton
theorem _root_.solution : su2Gen2 ≠ 0 := by
  intro h
  have := su2_bracket_12
  rw [h] at this
  simp only [lie_zero] at this
  exact su2Gen3_ne_zero this.symm
end Newton
