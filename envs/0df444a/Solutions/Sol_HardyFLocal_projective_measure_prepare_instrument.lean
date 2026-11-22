-- Prove2me | solution 1 for HardyFLocal.projective_measure_prepare_instrument
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T00:34:08.052355+00:00
-- url     : https://prove2.me/submissions/030dd0dc-bca9-45b9-a66f-d1d457cb2c46

import Definitions.Def_HardyFLocal_Instrument

namespace HardyFLocal
open scoped Matrix ComplexOrder
private abbrev BoxMat := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

private theorem kraus_matrix_units {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    (∑ t : ι × ι, Matrix.single t.1 t.2 1 * A * Matrix.single t.2 t.1 1) = A.trace • 1 := by
  simp only [Fintype.sum_prod_type, Matrix.single_mul_mul_single, one_mul, mul_one]
  rw [Finset.sum_comm]
  simp_rw [show ∀ i j : ι, (Matrix.single i i (A j j) : Matrix ι ι ℂ) =
    A j j • Matrix.single i i 1 by intro i j; simp [Matrix.smul_single]]
  simp only [← Finset.smul_sum, Matrix.sum_single_one, ← Finset.sum_smul]
  rfl

private noncomputable def selectedBranch (P R : BoxMat) : Op (Fin 2 × Fin 2) where
  toFun A := (P * A).trace • R
  map_add' A B := by simp [mul_add, add_smul]
  map_smul' c A := by simp [smul_smul]

private theorem selected_cp (P R : BoxMat) (hp : P.IsHermitian) (hr : R.IsHermitian)
    (pp : P * P = P) (rr : R * R = R) : IsCP (selectedBranch P R) := by
  let K (t : (Fin 2 × Fin 2) × (Fin 2 × Fin 2)) : BoxMat := R * Matrix.single t.1 t.2 1 * P
  let e := Fintype.equivFin ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))
  refine ⟨_, K ∘ e.symm, fun A => ?_⟩
  have cyclic : (P * A * P).trace = (P * A).trace := by rw [Matrix.trace_mul_cycle, pp]
  calc
    selectedBranch P R A = R * ((P * A * P).trace • (1 : BoxMat)) * R := by
      simp [selectedBranch, cyclic, rr]
    _ = R * (∑ t : (Fin 2 × Fin 2) × (Fin 2 × Fin 2),
      Matrix.single t.1 t.2 1 * (P * A * P) * Matrix.single t.2 t.1 1) * R := by
      rw [kraus_matrix_units]
    _ = ∑ t, K t * A * (K t)ᴴ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun t _ => by
        simp [K, Matrix.conjTranspose_mul, hp.eq, hr.eq, Matrix.conjTranspose_single, mul_assoc]
    _ = ∑ i, (K ∘ e.symm) i * A * ((K ∘ e.symm) i)ᴴ :=
      (e.symm.sum_comp (fun t => K t * A * (K t)ᴴ)).symm

end HardyFLocal

open HardyFLocal
open scoped Matrix ComplexOrder

theorem solution
    (P R : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hp : P.IsHermitian) (hr : R.IsHermitian) (pp : P * P = P) (rr : R * R = R)
    (unitTrace : R.trace = 1) :
    ∃ I : Instrument,
      (∀ A, I.op 0 A = (P * A).trace • R) ∧
      (∀ A, I.op 1 A = ((1 - P) * A).trace • R) ∧
      (∀ n : ℕ, I.op (n + 2) = 0) := by
  let branch (n : ℕ) : Op (Fin 2 × Fin 2) :=
    if n = 0 then selectedBranch P R else if n = 1 then selectedBranch (1 - P) R else 0
  have restHerm : (1 - P).IsHermitian := Matrix.isHermitian_one.sub hp
  have restIdem : (1 - P) * (1 - P) = 1 - P := by
    rw [sub_mul, one_mul, mul_sub, mul_one, pp, sub_self, sub_zero]
  have cp (n) : IsCP (branch n) := by
    unfold branch
    split_ifs
    · exact selected_cp P R hp hr pp rr
    · exact selected_cp _ R restHerm hr restIdem rr
    · exact ⟨0, Fin.elim0, by simp⟩
  have norm (A : BoxMat) : HasSum (fun n => (branch n A).trace) A.trace := by
    have splitTrace : (P * A).trace + ((1 - P) * A).trace = A.trace := by
      rw [sub_mul, one_mul, Matrix.trace_sub, add_sub_cancel]
    rw [← splitTrace]
    apply ((hasSum_ite_eq (0 : ℕ) (P * A).trace).add
      (hasSum_ite_eq (1 : ℕ) ((1 - P) * A).trace)).congr_fun
    intro n
    by_cases h0 : n = 0 <;> by_cases h1 : n = 1 <;>
      simp_all [branch, selectedBranch, Matrix.trace_smul]
  exact ⟨⟨branch, cp, norm⟩, fun A => by simp [branch, selectedBranch],
    fun A => by simp [branch, selectedBranch], fun n => by simp [branch]⟩

