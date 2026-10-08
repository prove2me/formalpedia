-- Prove2me | solution 1 for MatousekLP.Integrality.append_unit_column_totallyUnimodular
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T04:02:09.42233+00:00
-- url     : https://prove2.me/submissions/caf5d85b-72ff-4da6-bd8f-3f7a68875df4

import Mathlib

open Matrix

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : A.IsTotallyUnimodular) (i : Fin m) :
    (Matrix.of fun r : Fin m =>
      (Fin.snoc (α := fun _ => ℝ) (A r) (if r = i then (1 : ℝ) else 0) : Fin (n + 1) → ℝ)
      ).IsTotallyUnimodular := by
  classical
  -- the unit column as a one-column matrix
  set B : Matrix (Fin m) (Fin 1) ℝ := fun r _ => if r = i then 1 else 0
  have hrow : (fromRows Aᵀ Bᵀ).IsTotallyUnimodular := by
    refine hA.transpose.fromRows_unitlike fun _ k => ⟨i, SignType.pos, ?_⟩
    funext r
    by_cases h : r = i
    · subst h; rw [Pi.single_eq_same, SignType.pos_eq_one, SignType.coe_one]
      show (if r = r then (1 : ℝ) else 0) = 1; simp
    · rw [Pi.single_eq_of_ne h]
      show (if r = i then (1 : ℝ) else 0) = 0; simp [h]
  have hcol : (fromCols A B).IsTotallyUnimodular := by
    rw [← transpose_isTotallyUnimodular_iff, transpose_fromCols]; exact hrow
  have heq : (Matrix.of fun r : Fin m =>
      (Fin.snoc (α := fun _ => ℝ) (A r) (if r = i then (1 : ℝ) else 0) : Fin (n + 1) → ℝ)) =
      (fromCols A B).submatrix id finSumFinEquiv.symm := by
    ext r j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [Matrix.of_apply, Fin.snoc_last, finSumFinEquiv_symm_last, submatrix_apply, id]
      rfl
    · simp [fromCols_apply_inl]
  rw [heq]
  exact hcol.submatrix _ _
