-- Prove2me | solution 1 for Newton.su2_bracket_23
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:48:47.482955+00:00
-- url     : https://prove2.me/submissions/68e95321-608c-469e-8d98-7091eb6e1ef6

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
import Theorems.Thm_Newton_SuNAlgebra_lie_def
import Theorems.Thm_Newton_SuNAlgebra_lie_matrix
attribute [local simp] Newton.SuNAlgebra.lie_matrix


section
open Matrix
namespace Newton
private theorem fin2_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp
private theorem pauliY_mul_pauliZ_00 : (pauliY * pauliZ) 0 0 = 0 := by
  rw [Matrix.mul_apply]; simp only [pauliY, pauliZ, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]; ring
private theorem pauliY_mul_pauliZ_01 : (pauliY * pauliZ) 0 1 = Complex.I := by
  rw [Matrix.mul_apply]; simp only [pauliY, pauliZ, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]; ring
private theorem pauliY_mul_pauliZ_10 : (pauliY * pauliZ) 1 0 = Complex.I := by
  rw [Matrix.mul_apply]; simp only [pauliY, pauliZ, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]; ring
private theorem pauliY_mul_pauliZ_11 : (pauliY * pauliZ) 1 1 = 0 := by
  rw [Matrix.mul_apply]; simp only [pauliY, pauliZ, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]; ring
private theorem pauliZ_mul_pauliY_00 : (pauliZ * pauliY) 0 0 = 0 := by
  rw [Matrix.mul_apply]; simp only [pauliY, pauliZ, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]; ring
private theorem pauliZ_mul_pauliY_01 : (pauliZ * pauliY) 0 1 = -Complex.I := by
  rw [Matrix.mul_apply]; simp only [pauliY, pauliZ, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]; ring
private theorem pauliZ_mul_pauliY_10 : (pauliZ * pauliY) 1 0 = -Complex.I := by
  rw [Matrix.mul_apply]; simp only [pauliY, pauliZ, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]; ring
private theorem pauliZ_mul_pauliY_11 : (pauliZ * pauliY) 1 1 = 0 := by
  rw [Matrix.mul_apply]; simp only [pauliY, pauliZ, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]; ring
private theorem pauliYZ_comm_00 :
    (pauliY * pauliZ - pauliZ * pauliY) 0 0 = ((2 * Complex.I) • pauliX) 0 0 := by
  rw [Matrix.sub_apply, Matrix.smul_apply]; simp only [pauliX, smul_eq_mul,
             cons_val_zero, pauliY_mul_pauliZ_00, pauliZ_mul_pauliY_00]; ring
private theorem pauliYZ_comm_01 :
    (pauliY * pauliZ - pauliZ * pauliY) 0 1 = ((2 * Complex.I) • pauliX) 0 1 := by
  rw [Matrix.sub_apply, Matrix.smul_apply]; simp only [pauliX, smul_eq_mul,
             cons_val_zero, cons_val_one,
             pauliY_mul_pauliZ_01, pauliZ_mul_pauliY_01]; ring
private theorem pauliYZ_comm_10 :
    (pauliY * pauliZ - pauliZ * pauliY) 1 0 = ((2 * Complex.I) • pauliX) 1 0 := by
  rw [Matrix.sub_apply, Matrix.smul_apply]; simp only [pauliX, smul_eq_mul,
             cons_val_zero, cons_val_one,
             pauliY_mul_pauliZ_10, pauliZ_mul_pauliY_10]; ring
private theorem pauliYZ_comm_11 :
    (pauliY * pauliZ - pauliZ * pauliY) 1 1 = ((2 * Complex.I) • pauliX) 1 1 := by
  rw [Matrix.sub_apply, Matrix.smul_apply]; simp only [pauliX, smul_eq_mul,
             cons_val_zero, cons_val_one,
             pauliY_mul_pauliZ_11, pauliZ_mul_pauliY_11]; ring
private theorem pauliY_pauliZ_commutator :
    pauliY * pauliZ - pauliZ * pauliY = (2 * Complex.I) • pauliX := by
  ext i j
  rcases fin2_eq_zero_or_one i with hi | hi <;>
  rcases fin2_eq_zero_or_one j with hj | hj <;>
  simp only [hi, hj, pauliYZ_comm_00, pauliYZ_comm_01, pauliYZ_comm_10, pauliYZ_comm_11]
end Newton
end

set_option autoImplicit false
open Matrix
open Newton
namespace Newton
theorem _root_.solution : ⁅su2Gen2, su2Gen3⁆ = su2Gen1 := by
  apply SuNAlgebra.ext
  simp only [SuNAlgebra.lie_def, su2Gen1, su2Gen2, su2Gen3,
             su2Gen1Matrix, su2Gen2Matrix, su2Gen3Matrix]
  have h1 : (-Complex.I / 2 : ℂ) • pauliY * ((-Complex.I / 2 : ℂ) • pauliZ) =
      ((-Complex.I / 2) * (-Complex.I / 2)) • (pauliY * pauliZ) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h2 : (-Complex.I / 2 : ℂ) • pauliZ * ((-Complex.I / 2 : ℂ) • pauliY) =
      ((-Complex.I / 2) * (-Complex.I / 2)) • (pauliZ * pauliY) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h1, h2, ← smul_sub, pauliY_pauliZ_commutator, smul_smul]
  have hcoef : (-Complex.I / 2) * (-Complex.I / 2) * (2 * Complex.I) = -Complex.I / 2 := by
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, hI2]; ring
    ring_nf; rw [hI3]; ring
  rw [hcoef]
end Newton
