-- Prove2me | solution 1 for MatrixCompletion.NoSpuriousMin.K_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-13T19:10:00.908459+00:00
-- url     : https://prove2.me/submissions/950b8849-ef45-45a8-9e86-553360e20a03

import Definitions.Def_MCNoSpuriousMinModel

open Matrix MatrixCompletion.NoSpuriousMin

namespace KDecomp

variable {m n d r : ℕ}

/-! ### Bilinear algebra of the Frobenius pairing -/

lemma innerM_comm (A B : Matrix (Fin m) (Fin n) ℝ) : innerM A B = innerM B A := by
  simp only [innerM]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _

lemma frobSq_eq_innerM (A : Matrix (Fin m) (Fin n) ℝ) : frobSq A = innerM A A := by
  simp only [frobSq, innerM, sq]

lemma innerM_add_left (A B C : Matrix (Fin m) (Fin n) ℝ) :
    innerM (A + B) C = innerM A C + innerM B C := by
  simp only [innerM, Matrix.add_apply, add_mul, ← Finset.sum_add_distrib]

lemma innerM_add_right (A B C : Matrix (Fin m) (Fin n) ℝ) :
    innerM A (B + C) = innerM A B + innerM A C := by
  rw [innerM_comm A (B + C), innerM_add_left, innerM_comm B A, innerM_comm C A]

lemma innerM_smul_left (c : ℝ) (A B : Matrix (Fin m) (Fin n) ℝ) :
    innerM (c • A) B = c * innerM A B := by
  simp only [innerM, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

lemma innerM_neg_left (A B : Matrix (Fin m) (Fin n) ℝ) :
    innerM (-A) B = -innerM A B := by
  simp only [innerM, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]

lemma frobSq_add (A B : Matrix (Fin m) (Fin n) ℝ) :
    frobSq (A + B) = frobSq A + 2 * innerM A B + frobSq B := by
  simp only [frobSq, innerM, Matrix.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The trace identity `⟨M X, W⟩ = ⟨M, W Xᵀ⟩`. -/
lemma innerM_mul_transpose (M : Matrix (Fin d) (Fin d) ℝ) (X W : Matrix (Fin d) (Fin r) ℝ) :
    innerM (M * X) W = innerM M (W * Xᵀ) := by
  simp only [innerM, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

lemma innerM_transpose (A B : Matrix (Fin d) (Fin d) ℝ) : innerM Aᵀ Bᵀ = innerM A B := by
  simp only [innerM, Matrix.transpose_apply]
  exact Finset.sum_comm

/-! ### The sampling projection `P_Ω` -/

lemma projSet_add (Ω : Finset (Fin d × Fin d)) (A B : Matrix (Fin d) (Fin d) ℝ) :
    projSet Ω (A + B) = projSet Ω A + projSet Ω B := by
  ext i j
  by_cases h : (i, j) ∈ Ω <;> simp [projSet, h]

lemma projSet_neg (Ω : Finset (Fin d × Fin d)) (A : Matrix (Fin d) (Fin d) ℝ) :
    projSet Ω (-A) = -projSet Ω A := by
  ext i j
  by_cases h : (i, j) ∈ Ω <;> simp [projSet, h]

/-- `P_Ω` is self-adjoint for the Frobenius pairing. -/
lemma innerM_projSet_left (Ω : Finset (Fin d × Fin d)) (A B : Matrix (Fin d) (Fin d) ℝ) :
    innerM (projSet Ω A) B = innerM A (projSet Ω B) := by
  simp only [innerM, projSet, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : (i, j) ∈ Ω <;> simp [h]

lemma projSet_idem (Ω : Finset (Fin d × Fin d)) (A : Matrix (Fin d) (Fin d) ℝ) :
    projSet Ω (projSet Ω A) = projSet Ω A := by
  ext i j
  by_cases h : (i, j) ∈ Ω <;> simp [projSet, h]

/-- For a symmetric index set, `P_Ω` commutes with transposition. -/
lemma projSet_transpose (Ω : Finset (Fin d × Fin d))
    (hsym : ∀ i j : Fin d, (i, j) ∈ Ω ↔ (j, i) ∈ Ω) (A : Matrix (Fin d) (Fin d) ℝ) :
    (projSet Ω A)ᵀ = projSet Ω Aᵀ := by
  ext i j
  simp only [Matrix.transpose_apply, projSet, Matrix.of_apply]
  by_cases h : (i, j) ∈ Ω
  · simp [h, (hsym i j).mp h]
  · have h' : (j, i) ∉ Ω := fun hc => h ((hsym j i).mp hc)
    simp [h, h']

end KDecomp

open KDecomp

theorem solution {d r : ℕ} (Z X U : Matrix (Fin d) (Fin r) ℝ) (Ω : Finset (Fin d × Fin d))
    (lam α : ℝ)
    (hsym : ∀ i j : Fin d, (i, j) ∈ Ω ↔ (j, i) ∈ Ω)
    (hU : U * Uᵀ = Z * Zᵀ) :
    Kfun Z Ω lam α X U =
      frobSq (projSet Ω ((X - U) * (X - U)ᵀ))
        - 3 * frobSq (projSet Ω (X * Xᵀ - U * Uᵀ))
        + lam * (regHessQF α X (X - U) - 4 * innerM (regGrad α X) (X - U)) := by
  -- Unfold the objective's Hessian/gradient and eliminate `Z` via `U Uᵀ = Z Zᵀ`.
  simp only [Kfun, hessQF, objGrad]
  rw [← hU]
  -- `U Uᵀ − X Xᵀ = −(X Xᵀ − U Uᵀ)` and the polarization identity
  -- `D Xᵀ + X Dᵀ = D Dᵀ + E`, where `D = X − U` and `E = X Xᵀ − U Uᵀ`.
  have hflipsign : U * Uᵀ - X * Xᵀ = -(X * Xᵀ - U * Uᵀ) := by abel
  have hpol : (X - U) * Xᵀ + X * (X - U)ᵀ
      = (X - U) * (X - U)ᵀ + (X * Xᵀ - U * Uᵀ) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.transpose_sub]
    abel
  rw [hflipsign, projSet_neg, hpol, projSet_add]
  -- Abbreviations.
  set D : Matrix (Fin d) (Fin r) ℝ := X - U with hD
  set E : Matrix (Fin d) (Fin d) ℝ := X * Xᵀ - U * Uᵀ with hE
  set P : Matrix (Fin d) (Fin d) ℝ := projSet Ω E with hP
  set Q : Matrix (Fin d) (Fin d) ℝ := projSet Ω (D * Dᵀ) with hQ
  -- `E` is symmetric, hence so is `P` (using the symmetry of `Ω`).
  have hEsymm : Eᵀ = E := by
    rw [hE, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_transpose]
  have hPsymm : Pᵀ = P := by rw [hP, projSet_transpose Ω hsym, hEsymm]
  -- `⟨Q, P⟩ = ⟨P, D Dᵀ⟩`, since `P_Ω` is idempotent and self-adjoint.
  have hQP : innerM Q P = innerM P (D * Dᵀ) := by
    rw [hQ, hP, innerM_projSet_left, projSet_idem, innerM_comm]
  -- `⟨P, E⟩ = ‖P‖_F²`.
  have hPE : innerM P E = frobSq P := by
    rw [frobSq_eq_innerM, hP, innerM_projSet_left, innerM_projSet_left, projSet_idem]
  -- The first-order term: `⟨P X, D⟩ = ½ (⟨P, D Dᵀ⟩ + ‖P‖_F²)`.
  have hgrad : innerM (P * X) D = (innerM P (D * Dᵀ) + frobSq P) / 2 := by
    have hswap : innerM P (X * Dᵀ) = innerM P (D * Xᵀ) := by
      have h1 : innerM P (X * Dᵀ) = innerM Pᵀ (X * Dᵀ)ᵀ := (innerM_transpose _ _).symm
      rw [h1, hPsymm, Matrix.transpose_mul, Matrix.transpose_transpose]
    have h2 : innerM P (D * Xᵀ) + innerM P (X * Dᵀ) = innerM P (D * Dᵀ) + innerM P E := by
      rw [← innerM_add_right, hpol, innerM_add_right]
    rw [hswap, hPE] at h2
    rw [innerM_mul_transpose]
    linarith
  -- Assemble: expand the square, the gradient pairing, and cancel.
  rw [frobSq_add, hQP, innerM_neg_left, innerM_add_left, innerM_smul_left, innerM_smul_left,
    hgrad]
  ring
