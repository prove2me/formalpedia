-- Prove2me | solution 1 for HryniewiczCriterion.eigenAngleSum_graphUnitary4_blockOne
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T23:05:11.887915+00:00
-- url     : https://prove2.me/submissions/5a60061a-4bc6-4117-8a2f-efe9a555c9c0

import Mathlib
import Mathlib.LinearAlgebra.Matrix.Invertible
import Definitions.Def_HryniewiczCriterion_GraphAngle

open Matrix HryniewiczCriterion

theorem angle_blocks (V : Matrix (Fin 2) (Fin 2) ℂ) :
    eigenAngleSum (fromBlocks (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 V) =
      4 * Real.pi + eigenAngleSum V := by
  unfold eigenAngleSum
  rw [charpoly_fromBlocks_zero₂₁, Polynomial.roots_mul (mul_ne_zero (charpoly_monic _).ne_zero (charpoly_monic _).ne_zero),
    charpoly_one]
  rw [Polynomial.roots_pow, show (1 : Polynomial ℂ) = Polynomial.C 1 from rfl, Polynomial.roots_X_sub_C]
  simp [Fintype.card_fin,
    angPos, Complex.arg_one, two_smul, Multiset.map_add, Multiset.sum_add]
  ring

theorem angle_zero (n : ℕ) : eigenAngleSum (0 : Matrix (Fin n) (Fin n) ℂ) = (n : ℝ) * (2 * Real.pi) := by
  simp [eigenAngleSum, charpoly_zero, Polynomial.roots_X_pow, Multiset.map_nsmul, Multiset.sum_nsmul,
    angPos, Complex.arg_zero, nsmul_eq_mul]

def colEquiv : Fin 4 ≃ (Fin 2 ⊕ Fin 2) := (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin (2 + 2)).symm
def rowEquiv : Fin 4 ≃ (Fin 2 ⊕ Fin 2) := (Equiv.swap 1 2).trans colEquiv

theorem basis_blocks (g : Matrix (Fin 2) (Fin 2) ℝ) :
    reindex rowEquiv colEquiv (graphBasis4 (blockOne g)) =
      fromBlocks (graphBasis2 1) 0 0 (graphBasis2 g) := by
  ext r c
  rcases r with r | r <;> rcases c with c | c <;> fin_cases r <;> fin_cases c <;>
    norm_num [reindex_apply, rowEquiv, colEquiv, graphBasis4, graphBasis2, blockOne,
      fromBlocks, finSumFinEquiv, Equiv.swap_apply_def, Fin.castAdd, Fin.addNat, Fin.castLE,
      Matrix.one_apply, Fin.ext_iff, Matrix.cons_val_two, Matrix.cons_val_three]

#print axioms basis_blocks

theorem reindex_mul' {a b c d e f : Type*} [Fintype b] [Fintype e]
    (r : a ≃ d) (s : b ≃ e) (t : c ≃ f) (A : Matrix a b ℂ) (B : Matrix b c ℂ) :
    reindex r s A * reindex s t B = reindex r t (A * B) := by
  simp [reindex_apply, submatrix_mul_equiv]

theorem lag_reindex {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (r c : a ≃ b) (A : Matrix a a ℂ) :
    lagUnitary (reindex r c A) = reindex r r (lagUnitary A) := by
  unfold lagUnitary
  rw [conjTranspose_reindex, reindex_mul', inv_reindex, transpose_reindex,
    reindex_mul', reindex_mul']

theorem lag_blocks (A B : Matrix (Fin 2) (Fin 2) ℂ) (hA : IsUnit A) (hB : IsUnit B) :
    lagUnitary (fromBlocks A 0 0 B) = fromBlocks (lagUnitary A) 0 0 (lagUnitary B) := by
  have hgA : IsUnit (A.conjTranspose * A) := ((isUnit_conjTranspose A).mpr hA).mul hA
  have hgB : IsUnit (B.conjTranspose * B) := ((isUnit_conjTranspose B).mpr hB).mul hB
  unfold lagUnitary
  rw [fromBlocks_conjTranspose, fromBlocks_transpose]
  simp only [conjTranspose_zero, transpose_zero, fromBlocks_multiply, mul_zero, zero_mul, add_zero, zero_add]
  rw [inv_fromBlocks_zero₂₁_of_isUnit_iff _ _ _ (iff_of_true hgA hgB)]
  simp only [mul_zero, zero_mul, neg_zero, fromBlocks_multiply, add_zero, zero_add]

#print axioms lag_blocks

theorem lag_isUnit {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (h : IsUnit A) : IsUnit (lagUnitary A) := by
  exact (h.mul (isUnit_nonsing_inv_iff.mpr (((isUnit_conjTranspose A).mpr h).mul h))).mul
    ((isUnit_transpose A).mpr h)

theorem lag_nonunit {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (h : ¬IsUnit A) : lagUnitary A = 0 := by
  have hd : A.det = 0 := by
    simpa [isUnit_iff_isUnit_det, isUnit_iff_ne_zero] using h
  have hg : ¬IsUnit (A.conjTranspose * A).det := by
    simp [det_mul, hd, isUnit_iff_ne_zero]
  simp [lagUnitary, nonsing_inv_apply_not_isUnit _ hg]

theorem basis_one_unit : IsUnit (graphBasis2 (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  norm_num [graphBasis2, det_fin_two, Matrix.one_apply, Matrix.cons_val_two]

theorem blockOne_one : blockOne (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [blockOne, Matrix.one_apply,
    Matrix.cons_val_two, Matrix.cons_val_three]

theorem graph_blocks (g : Matrix (Fin 2) (Fin 2) ℝ) (hg : IsUnit (graphBasis2 g)) :
    reindex rowEquiv rowEquiv (graphUnitary4 (blockOne g)) =
      fromBlocks 1 0 0 (graphUnitary2 g) := by
  have hbase := basis_blocks (1 : Matrix (Fin 2) (Fin 2) ℝ)
  rw [blockOne_one] at hbase
  have hlag : IsUnit (lagUnitary (graphBasis2 (1 : Matrix (Fin 2) (Fin 2) ℝ))) :=
    lag_isUnit _ basis_one_unit
  unfold graphUnitary4 graphUnitary2
  rw [← reindex_mul' rowEquiv rowEquiv rowEquiv, ← inv_reindex, ← lag_reindex rowEquiv colEquiv,
    ← lag_reindex rowEquiv colEquiv, basis_blocks, hbase,
    lag_blocks _ _ basis_one_unit hg, lag_blocks _ _ basis_one_unit basis_one_unit]
  rw [inv_fromBlocks_zero₂₁_of_isUnit_iff _ _ _ (iff_of_true hlag hlag)]
  simp [fromBlocks_multiply, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hlag)]

theorem graph_nonunit (g : Matrix (Fin 2) (Fin 2) ℝ) (hg : ¬IsUnit (graphBasis2 g)) :
    graphUnitary4 (blockOne g) = 0 ∧ graphUnitary2 g = 0 := by
  have h4 : ¬IsUnit (graphBasis4 (blockOne g)) := by
    intro h
    have hd : (reindex rowEquiv colEquiv (graphBasis4 (blockOne g))).det ≠ 0 := by
      rw [det_reindex]
      exact mul_ne_zero (by simp) (isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det _).mp h))
    rw [basis_blocks] at hd
    exact hg ((isUnit_fromBlocks_zero₂₁.mp ((isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr hd))).2)
  simp [graphUnitary4, graphUnitary2, lag_nonunit _ h4, lag_nonunit _ hg]

theorem solution (g : Matrix (Fin 2) (Fin 2) ℝ) :
    eigenAngleSum (graphUnitary4 (blockOne g)) = 4 * Real.pi + eigenAngleSum (graphUnitary2 g) := by
  by_cases hg : IsUnit (graphBasis2 g)
  · have he : eigenAngleSum (graphUnitary4 (blockOne g)) =
        eigenAngleSum (reindex rowEquiv rowEquiv (graphUnitary4 (blockOne g))) := by
      unfold eigenAngleSum
      rw [charpoly_reindex]
    rw [he, graph_blocks g hg, angle_blocks]
  · obtain ⟨h4, h2⟩ := graph_nonunit g hg
    rw [h4, h2, angle_zero, angle_zero]
    norm_num
    ring

#print axioms solution

