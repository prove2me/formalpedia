-- Prove2me | solution 1 for Newton.su2_bracket_12
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:42:54.821869+00:00
-- url     : https://prove2.me/submissions/f828f7bf-7ff8-429e-a42b-25507a15020d

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
import Theorems.Thm_Newton_SuNAlgebra_lie_def
import Theorems.Thm_Newton_SuNAlgebra_lie_matrix
attribute [local simp] Newton.SuNAlgebra.lie_matrix


section
open Matrix
namespace Newton
private theorem pauliX_mul_pauliY_00 : (pauliX * pauliY) 0 0 = Complex.I := by
  rw [Matrix.mul_apply]; simp only [pauliX, pauliY, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]
  ring
private theorem pauliX_mul_pauliY_01 : (pauliX * pauliY) 0 1 = 0 := by
  rw [Matrix.mul_apply]; simp only [pauliX, pauliY, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]
  ring
private theorem pauliX_mul_pauliY_10 : (pauliX * pauliY) 1 0 = 0 := by
  rw [Matrix.mul_apply]; simp only [pauliX, pauliY, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]
  ring
private theorem pauliX_mul_pauliY_11 : (pauliX * pauliY) 1 1 = -Complex.I := by
  rw [Matrix.mul_apply]; simp only [pauliX, pauliY, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]
  ring
private theorem pauliY_mul_pauliX_00 : (pauliY * pauliX) 0 0 = -Complex.I := by
  rw [Matrix.mul_apply]; simp only [pauliX, pauliY, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]
  ring
private theorem pauliY_mul_pauliX_01 : (pauliY * pauliX) 0 1 = 0 := by
  rw [Matrix.mul_apply]; simp only [pauliX, pauliY, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]
  ring
private theorem pauliY_mul_pauliX_10 : (pauliY * pauliX) 1 0 = 0 := by
  rw [Matrix.mul_apply]; simp only [pauliX, pauliY, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]
  ring
private theorem pauliY_mul_pauliX_11 : (pauliY * pauliX) 1 1 = Complex.I := by
  rw [Matrix.mul_apply]; simp only [pauliX, pauliY, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]
  ring
private theorem fin2_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp
private theorem pauliXY_comm_00 :
    (pauliX * pauliY - pauliY * pauliX) 0 0 = ((2 * Complex.I) • pauliZ) 0 0 := by
  rw [Matrix.sub_apply, Matrix.smul_apply]; simp only [pauliZ, smul_eq_mul,
             cons_val_zero, pauliX_mul_pauliY_00, pauliY_mul_pauliX_00]
  ring
private theorem pauliXY_comm_01 :
    (pauliX * pauliY - pauliY * pauliX) 0 1 = ((2 * Complex.I) • pauliZ) 0 1 := by
  rw [Matrix.sub_apply, Matrix.smul_apply]; simp only [pauliZ, smul_eq_mul,
             cons_val_zero, cons_val_one,
             pauliX_mul_pauliY_01, pauliY_mul_pauliX_01]
  ring
private theorem pauliXY_comm_10 :
    (pauliX * pauliY - pauliY * pauliX) 1 0 = ((2 * Complex.I) • pauliZ) 1 0 := by
  rw [Matrix.sub_apply, Matrix.smul_apply]; simp only [pauliZ, smul_eq_mul,
             cons_val_zero, cons_val_one,
             pauliX_mul_pauliY_10, pauliY_mul_pauliX_10]
  ring
private theorem pauliXY_comm_11 :
    (pauliX * pauliY - pauliY * pauliX) 1 1 = ((2 * Complex.I) • pauliZ) 1 1 := by
  rw [Matrix.sub_apply, Matrix.smul_apply]; simp only [pauliZ, smul_eq_mul,
             cons_val_zero, cons_val_one,
             pauliX_mul_pauliY_11, pauliY_mul_pauliX_11]
  ring
private theorem pauliX_pauliY_commutator :
    pauliX * pauliY - pauliY * pauliX = (2 * Complex.I) • pauliZ := by
  ext i j
  rcases fin2_eq_zero_or_one i with hi | hi <;>
  rcases fin2_eq_zero_or_one j with hj | hj <;>
  simp only [hi, hj, pauliXY_comm_00, pauliXY_comm_01, pauliXY_comm_10, pauliXY_comm_11]
end Newton
end

set_option autoImplicit false
open Matrix
open Newton
namespace Newton
theorem _root_.solution : ⁅su2Gen1, su2Gen2⁆ = su2Gen3 := by
  apply SuNAlgebra.ext
  simp only [SuNAlgebra.lie_def, su2Gen1, su2Gen2, su2Gen3,
             su2Gen1Matrix, su2Gen2Matrix, su2Gen3Matrix]
  -- (-I/2) • σ₁ * (-I/2) • σ₂ - (-I/2) • σ₂ * (-I/2) • σ₁
  -- = (-I/2)² (σ₁ σ₂ - σ₂ σ₁) = (-1/4) [σ₁, σ₂]
  have h1 : (-Complex.I / 2 : ℂ) • pauliX * ((-Complex.I / 2 : ℂ) • pauliY) =
      ((-Complex.I / 2) * (-Complex.I / 2)) • (pauliX * pauliY) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h2 : (-Complex.I / 2 : ℂ) • pauliY * ((-Complex.I / 2 : ℂ) • pauliX) =
      ((-Complex.I / 2) * (-Complex.I / 2)) • (pauliY * pauliX) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h1, h2, ← smul_sub, pauliX_pauliY_commutator, smul_smul]
  -- Calculate coefficient: (-I/2)² * 2I = (-1/4) * 2I = -I/2
  have hcoef : (-Complex.I / 2) * (-Complex.I / 2) * (2 * Complex.I) = -Complex.I / 2 := by
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, hI2]; ring
    ring_nf
    rw [hI3]
    ring
  rw [hcoef]
end Newton
