-- Prove2me | solution 1 for NetPriceDisc.Random.eq_12_rayleigh
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:54:44.282978+00:00
-- url     : https://prove2.me/submissions/0b637c76-e422-4bce-bf74-34f2bb47855f

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

theorem solution {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : ∀ i j, 0 ≤ G i j) :
    walks (G + Gᵀ) 1 / (ones n ⬝ᵥ ones n) ≤ specNorm (G + Gᵀ) := by
  rw [ones_dot]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, div_zero]; exact norm_nonneg _
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hn']
    have := walks_le (G + Gᵀ) 1
    simpa [specNorm] using this
