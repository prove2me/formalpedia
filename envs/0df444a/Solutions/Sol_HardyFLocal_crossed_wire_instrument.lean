-- Prove2me | solution 1 for HardyFLocal.crossed_wire_instrument
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T01:05:48.589329+00:00
-- url     : https://prove2.me/submissions/c36fd54e-6d34-472a-9cf6-b5f5829a90a6

import Mathlib
import Definitions.Def_HardyFLocal_Lattice
import Theorems.Thm_HardyFLocal_prodOp_apply_kron
import Theorems.Thm_HardyFLocal_projective_measure_prepare_instrument
open scoped Kronecker Matrix
namespace HardyFLocal
open scoped Kronecker Matrix
open HardyCausaloid

private noncomputable def probeBranch (P R : Matrix (Fin 2) (Fin 2) ℂ) : Op (Fin 2) where
  toFun A := (P * A).trace • R
  map_add' A B := by simp [mul_add,add_smul]
  map_smul' c A := by simp [smul_smul]

private theorem product_op_ext (F G : Op (Fin 2 × Fin 2))
    (h : ∀ A B : Matrix (Fin 2) (Fin 2) ℂ, F (A ⊗ₖ B) = G (A ⊗ₖ B)) : F = G := by
  apply LinearMap.ext
  intro M
  rw [Matrix.matrix_eq_sum_single M]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  rintro ⟨i,j⟩ _
  apply Finset.sum_congr rfl
  rintro ⟨k,l⟩ _
  have eqUnit : Matrix.single (i,j) (k,l) (M (i,j) (k,l)) =
      Matrix.single i k (M (i,j) (k,l)) ⊗ₖ Matrix.single j l (1 : ℂ) := by
    simp [Matrix.single_kronecker_single]
  rw [eqUnit,h]

end HardyFLocal

open HardyFLocal

open Classical in
theorem solution (P Q R T : Matrix (Fin 2) (Fin 2) ℂ)
    (hp : P.IsHermitian) (hq : Q.IsHermitian) (hr : R.IsHermitian) (ht : T.IsHermitian)
    (ep : P * P = P) (eq : Q * Q = Q) (er : R * R = R) (et : T * T = T)
    (tr : R.trace = 1) (tt : T.trace = 1) :
    ∃ (I : Instrument) (F G : Op (Fin 2)), I.op 0 = prodOp F G ∧
      (∀ A, F A = (P * A).trace • R) ∧ (∀ B, G B = (Q * B).trace • T) := by
  have herm {A B : Matrix (Fin 2) (Fin 2) ℂ} (ha : A.IsHermitian) (hb : B.IsHermitian) :
      (A ⊗ₖ B).IsHermitian := by rw [Matrix.IsHermitian,Matrix.conjTranspose_kronecker,ha.eq,hb.eq]
  obtain ⟨I,sel,_⟩ := projective_measure_prepare_instrument (P ⊗ₖ Q) (R ⊗ₖ T)
    (herm hp hq) (herm hr ht) (by rw [← Matrix.mul_kronecker_mul,ep,eq])
    (by rw [← Matrix.mul_kronecker_mul,er,et]) (by simp [Matrix.trace_kronecker,tr,tt])
  refine ⟨I,probeBranch P R,probeBranch Q T,?_,fun _ => rfl,fun _ => rfl⟩
  apply product_op_ext
  intro A B
  rw [sel,prodOp_apply_kron,← Matrix.mul_kronecker_mul,Matrix.trace_kronecker]
  apply Matrix.ext
  rintro ⟨i,j⟩ ⟨k,l⟩
  simp [probeBranch,Matrix.smul_apply]
  ring

