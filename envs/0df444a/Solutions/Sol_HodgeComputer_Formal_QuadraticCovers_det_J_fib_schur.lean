-- Prove2me | solution 1 for HodgeComputer.Formal.QuadraticCovers.det_J_fib_schur
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T03:32:30.766495+00:00
-- url     : https://prove2.me/submissions/a46434fa-a519-4b9f-b937-35779a941357

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators Matrix

namespace HodgeComputerFormalSchurAux
theorem det_J_fib_schur {R : Type*} [CommRing R] (M : Matrix (Fin 4) (Fin 4) R)
    (a' b' v' E3_dot : R)
    (h00 : M 0 0 = 0) (h01 : M 0 1 = 0)
    (h0 : M 0 2 + M 0 3 * v' = 0)
    (h1 : M 1 0 * a' + M 1 1 * b' + M 1 2 + M 1 3 * v' = 0)
    (h2 : M 2 0 * a' + M 2 1 * b' + M 2 2 + M 2 3 * v' = 0)
    (h3 : M 3 0 * a' + M 3 1 * b' + M 3 2 + M 3 3 * v' = E3_dot) :
    M.det = M 0 3 * (M 1 1 * M 2 0 - M 1 0 * M 2 1) * E3_dot := by
  let Rmat : Matrix (Fin 4) (Fin 4) R :=
    Matrix.of ![![1, 0, a', 0],
                ![0, 1, b', 0],
                ![0, 0, 1, 0],
                ![0, 0, v', 1]]
  have hRdet : Rmat.det = 1 := by
    rw [Matrix.det_succ_column_zero]
    simp only [Fin.sum_univ_four, Rmat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      Fin.val_zero, Fin.val_one, Fin.val_two, show (3 : Fin 4).val = 3 from rfl,
      pow_zero, one_mul, Fin.isValue]
    have hsub : Rmat.submatrix (Fin.succAbove 0) Fin.succ =
        Matrix.of ![![1, b', 0], ![0, 1, 0], ![0, v', 1]] := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [hsub]
    simp only [Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    ring
  let Mres : Matrix (Fin 4) (Fin 4) R :=
    Matrix.of ![![0, 0, 0, M 0 3],
                ![M 1 0, M 1 1, 0, M 1 3],
                ![M 2 0, M 2 1, 0, M 2 3],
                ![M 3 0, M 3 1, E3_dot, M 3 3]]
  have hMR : M * Rmat = Mres := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;>
      (simp only [Rmat, Mres, Matrix.of_apply, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
         Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
         Matrix.head_cons, Matrix.tail_cons, Fin.isValue, mul_one, mul_zero, zero_mul,
         add_zero, zero_add, h00, h01])
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have hdet : M.det = (M * Rmat).det := by rw [Matrix.det_mul, hRdet, mul_one]
  rw [hdet, hMR, Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four, Mres, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    Fin.val_zero, Fin.val_one, Fin.val_two, show (3 : Fin 4).val = 3 from rfl,
    Fin.isValue]
  have hsub : Mres.submatrix Fin.succ (Fin.succAbove 3) =
      Matrix.of ![![M 1 0, M 1 1, 0], ![M 2 0, M 2 1, 0], ![M 3 0, M 3 1, E3_dot]] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [hsub]
  simp only [Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
  ring

end HodgeComputerFormalSchurAux

theorem solution
    {R : Type*} [CommRing R] (M : Matrix (Fin 4) (Fin 4) R)
    (a' b' v' E3_dot : R)
    (h00 : M 0 0 = 0) (h01 : M 0 1 = 0)
    (h0 : M 0 2 + M 0 3 * v' = 0)
    (h1 : M 1 0 * a' + M 1 1 * b' + M 1 2 + M 1 3 * v' = 0)
    (h2 : M 2 0 * a' + M 2 1 * b' + M 2 2 + M 2 3 * v' = 0)
    (h3 : M 3 0 * a' + M 3 1 * b' + M 3 2 + M 3 3 * v' = E3_dot) :
    M.det = M 0 3 * (M 1 1 * M 2 0 - M 1 0 * M 2 1) * E3_dot :=
  HodgeComputerFormalSchurAux.det_J_fib_schur M a' b' v' E3_dot h00 h01 h0 h1 h2 h3
