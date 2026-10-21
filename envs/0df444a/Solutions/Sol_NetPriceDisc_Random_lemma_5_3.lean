-- Prove2me | solution 1 for NetPriceDisc.Random.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:55:43.346762+00:00
-- url     : https://prove2.me/submissions/b0bdc686-98ef-4a73-b5d0-8e3b6d1364d1

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

lemma walks_split {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hs : Aᵀ = A) (s m : ℕ) :
    walks A (2 * s + m) = ((A ^ s) *ᵥ ones n) ⬝ᵥ ((A ^ m) *ᵥ ((A ^ s) *ᵥ ones n)) := by
  unfold walks
  have h1 : A ^ (2 * s + m) = A ^ s * A ^ m * A ^ s := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have h2 : ones n ᵥ* (A ^ s) = (A ^ s) *ᵥ ones n := by
    rw [← Matrix.mulVec_transpose, Matrix.transpose_pow, hs]
  rw [h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, h2]

theorem solution {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : ∀ i j, 0 ≤ G i j)
    (s k : ℕ) (hs : 1 ≤ s) (hk : 2 * s ≤ k) :
    walks (G + Gᵀ) k ≤ specNorm (G + Gᵀ) ^ (k - 2 * s) * walks (G + Gᵀ) (2 * s) := by
  have hsym : (G + Gᵀ)ᵀ = G + Gᵀ := by simp [add_comm]
  obtain ⟨m, rfl⟩ : ∃ m, k = 2 * s + m := ⟨k - 2 * s, by omega⟩
  rw [Nat.add_sub_cancel_left]
  set A := G + Gᵀ with hA
  set v := (A ^ s) *ᵥ ones n with hv
  have hw := walks_split A hsym s m
  have hw0 := walks_split A hsym s 0
  rw [← hv] at hw hw0
  simp only [add_zero, pow_zero, Matrix.one_mulVec] at hw0
  have hvv : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ^ 2 = v ⬝ᵥ v := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [dotProduct, sq]
  rw [hw, hw0, specNorm]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h := bil (A ^ m) v v
    have h2 : ‖A ^ m‖ ≤ ‖A‖ ^ m := norm_pow_le' _ hm
    have h3 : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ *
        ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ = v ⬝ᵥ v := by rw [← sq]; exact hvv
    calc _ ≤ |v ⬝ᵥ ((A ^ m) *ᵥ v)| := le_abs_self _
      _ ≤ _ := h
      _ = ‖A ^ m‖ * (v ⬝ᵥ v) := by rw [mul_assoc, h3]
      _ ≤ ‖A‖ ^ m * (v ⬝ᵥ v) :=
          mul_le_mul_of_nonneg_right h2 (by rw [← h3]; exact mul_self_nonneg _)
