-- Prove2me | solution 1 for NetPriceDisc.Random.footnote_6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:54:45.363329+00:00
-- url     : https://prove2.me/submissions/75db21bf-1b8e-4ba8-9027-c616a15f8b7f

import Mathlib
import Definitions.Def_NetPriceDisc_Random_Model

set_option autoImplicit false
open Matrix NetPriceDisc.Random
open scoped Matrix.Norms.L2Operator

lemma bil {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) :
    |x ⬝ᵥ (A *ᵥ y)| ≤ ‖A‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ *
      ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))‖ := by
  have h1 : ‖(WithLp.toLp 2 (A *ᵥ y) : EuclideanSpace ℝ (Fin n))‖ ≤
      ‖A‖ * ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))‖ :=
    Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))
  have h2 := abs_real_inner_le_norm (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))
    (WithLp.toLp 2 (A *ᵥ y) : EuclideanSpace ℝ (Fin n))
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h2
  simp only [star_trivial] at h2
  rw [dotProduct_comm] at h2
  calc |x ⬝ᵥ (A *ᵥ y)| ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ *
        ‖(WithLp.toLp 2 (A *ᵥ y) : EuclideanSpace ℝ (Fin n))‖ := h2
    _ ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ *
        (‖A‖ * ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))‖) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = _ := by ring

lemma nrm_ones (n : ℕ) : ‖(WithLp.toLp 2 (ones n) : EuclideanSpace ℝ (Fin n))‖ ^ 2 = n := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [ones]

lemma ones_dot (n : ℕ) : ones n ⬝ᵥ ones n = n := by simp [ones, dotProduct]

lemma walks_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    walks A k ≤ ‖A ^ k‖ * n := by
  have h := bil (A ^ k) (ones n) (ones n)
  have h2 := nrm_ones n
  have h3 : ‖(WithLp.toLp 2 (ones n) : EuclideanSpace ℝ (Fin n))‖ *
      ‖(WithLp.toLp 2 (ones n) : EuclideanSpace ℝ (Fin n))‖ = n := by rw [← sq]; exact h2
  calc walks A k ≤ |ones n ⬝ᵥ ((A ^ k) *ᵥ ones n)| := le_abs_self _
    _ ≤ _ := h
    _ = ‖A ^ k‖ * n := by rw [mul_assoc, h3]

lemma nrm_single {n : ℕ} (i : Fin n) :
    ‖(WithLp.toLp 2 (Pi.single i (1 : ℝ)) : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  have : ‖(WithLp.toLp 2 (Pi.single i (1 : ℝ)) : EuclideanSpace ℝ (Fin n))‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Pi.single_apply]
  nlinarith [norm_nonneg (WithLp.toLp 2 (Pi.single i (1 : ℝ)) : EuclideanSpace ℝ (Fin n))]

lemma entry_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : |A i j| ≤ ‖A‖ := by
  have h := bil A (Pi.single i 1) (Pi.single j 1)
  rw [nrm_single, nrm_single] at h
  have e : (Pi.single i (1 : ℝ) : Fin n → ℝ) ⬝ᵥ (A *ᵥ Pi.single j 1) = A i j := by
    simp [Matrix.mulVec_single_one]
  rw [e] at h
  simpa using h

theorem solution {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (hbin : ∀ i j, G i j = 0 ∨ G i j = 1) (hdiag : ∀ i, G i i = 0) (hG0 : G ≠ 0) :
    1 ≤ specNorm (G + Gᵀ) := by
  obtain ⟨i, j, hij⟩ : ∃ i j, G i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hG0 (by ext i j; exact h i j)
  have h1 : G i j = 1 := (hbin i j).resolve_left hij
  have h2 : 0 ≤ G j i := by rcases hbin j i with h | h <;> rw [h] <;> norm_num
  have h3 : |(G + Gᵀ) i j| ≤ ‖G + Gᵀ‖ := entry_le _ i j
  have h4 : (G + Gᵀ) i j = G i j + G j i := by simp
  rw [h4, h1] at h3
  have : (1 : ℝ) ≤ |1 + G j i| := by rw [abs_of_nonneg (by linarith)]; linarith
  exact le_trans this h3
