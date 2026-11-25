-- Prove2me | solution 1 for Newton.su2Gen3_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:16:56.526505+00:00
-- url     : https://prove2.me/submissions/3915c349-4d66-4dcb-ad85-24dff559eca9

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
import Theorems.Thm_Newton_SuNAlgebra_lie_matrix
attribute [local simp] Newton.SuNAlgebra.lie_matrix



set_option autoImplicit false
open Matrix
open Newton
namespace Newton
theorem _root_.solution : su2Gen3 ≠ 0 := by
  intro h
  have : su2Gen3.matrix = 0 := by rw [h]; rfl
  simp only [su2Gen3, su2Gen3Matrix] at this
  have h00 : ((-Complex.I / 2 : ℂ) • pauliZ) 0 0 = (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by
    rw [this]
  rw [Matrix.smul_apply, Matrix.zero_apply] at h00
  simp only [pauliZ, cons_val_zero, smul_eq_mul, mul_one] at h00
  have : (-Complex.I / 2 : ℂ) = 0 := h00
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  simp only [neg_eq_zero, div_eq_zero_iff, hI, h2, or_self] at this
end Newton
