-- Prove2me | solution 1 for NetPriceDisc.Random.eq_9
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:54:46.661336+00:00
-- url     : https://prove2.me/submissions/16dc360e-08f4-46ff-ae93-7793cd58688f

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

lemma vec_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) :
    ∀ i, 0 ≤ ((A ^ k) *ᵥ ones n) i := by
  induction k with
  | zero => intro i; simp [ones]
  | succ k ih =>
    intro i
    have : (A ^ (k + 1)) *ᵥ ones n = A *ᵥ ((A ^ k) *ᵥ ones n) := by
      rw [pow_succ', ← Matrix.mulVec_mulVec]
    rw [this]
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_nonneg (fun m _ => mul_nonneg (hA i m) (ih m))

lemma walks_pos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hs : ∀ i j, A i j = A j i) (hne : ∃ i j, 0 < A i j) (k : ℕ) (hk : 1 ≤ k) :
    0 < walks A k := by
  have hv : ∀ k, (A ^ (k + 1)) *ᵥ ones n = A *ᵥ ((A ^ k) *ᵥ ones n) := by
    intro k; rw [pow_succ', ← Matrix.mulVec_mulVec]
  have key : ∀ k, 1 ≤ k → ∃ i, 0 < ((A ^ k) *ᵥ ones n) i := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      obtain ⟨i, j, hij⟩ := hne
      refine ⟨i, ?_⟩
      rw [pow_one]
      simp only [Matrix.mulVec, dotProduct, ones, mul_one]
      calc (0 : ℝ) < A i j := hij
        _ ≤ _ := Finset.single_le_sum (f := fun j => A i j) (fun j _ => hA i j) (Finset.mem_univ j)
    | succ k hk ih =>
      obtain ⟨i, hi⟩ := ih
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hi' := hi
      rw [hv k'] at hi'
      simp only [Matrix.mulVec, dotProduct] at hi'
      obtain ⟨m, _, hm⟩ : ∃ m ∈ Finset.univ, 0 < A i m * ((A ^ k') *ᵥ ones n) m := by
        by_contra h
        push Not at h
        exact absurd hi' (not_lt.mpr (Finset.sum_nonpos h))
      have hAim : 0 < A i m := by
        by_contra hcon
        have h3 : A i m = 0 := le_antisymm (not_lt.mp hcon) (hA i m)
        rw [h3] at hm; simp at hm
      refine ⟨m, ?_⟩
      rw [hv (k' + 1)]
      have hw0 := vec_nonneg A hA (k' + 1)
      have hAmi : 0 < A m i := by rw [hs m i]; exact hAim
      simp only [Matrix.mulVec, dotProduct] at hw0 ⊢
      calc (0 : ℝ) < A m i * (∑ x, (A ^ (k' + 1)) i x * ones n x) := mul_pos hAmi hi
        _ ≤ _ := Finset.single_le_sum
            (f := fun l => A m l * ∑ x, (A ^ (k' + 1)) l x * ones n x)
            (fun l _ => mul_nonneg (hA m l) (hw0 l)) (Finset.mem_univ i)
  obtain ⟨i, hi⟩ := key k hk
  unfold walks
  simp only [dotProduct, ones, one_mul]
  exact Finset.sum_pos' (fun j _ => vec_nonneg A hA k j) ⟨i, Finset.mem_univ i, hi⟩


lemma walks_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (k : ℕ) :
    walks (c • A) k = c ^ k * walks A k := by
  unfold walks
  rw [smul_pow, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem solution {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : ∀ i j, 0 ≤ G i j) (hG0 : G ≠ 0)
    (k : ℕ) (hk : 0 < k) :
    0 < walks ((1 / specNorm (G + Gᵀ)) • (G + Gᵀ)) k ∧
      walks ((1 / specNorm (G + Gᵀ)) • (G + Gᵀ)) k ≤ n := by
  obtain ⟨i, j, hij⟩ : ∃ i j, G i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hG0 (by ext i j; exact h i j)
  have hA : ∀ i j, 0 ≤ (G + Gᵀ) i j := fun i j => by simp [hG i j, hG j i, add_nonneg]
  have hs : ∀ i j, (G + Gᵀ) i j = (G + Gᵀ) j i := fun i j => by simp [add_comm]
  have hpos : 0 < (G + Gᵀ) i j := by
    have h1 : 0 < G i j := lt_of_le_of_ne (hG i j) (Ne.symm hij)
    have : (G + Gᵀ) i j = G i j + G j i := by simp
    rw [this]; linarith [hG j i]
  have hnorm : 0 < specNorm (G + Gᵀ) := by
    have := entry_le (G + Gᵀ) i j
    rw [abs_of_pos hpos] at this
    unfold specNorm
    linarith
  rw [walks_smul]
  refine ⟨mul_pos (pow_pos (by positivity) k) (walks_pos _ hA hs ⟨i, j, hpos⟩ k hk), ?_⟩
  have hB : ‖(1 / specNorm (G + Gᵀ)) • (G + Gᵀ)‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    unfold specNorm at hnorm ⊢
    rw [one_div, inv_mul_cancel₀ hnorm.ne']
  have hBk : ‖((1 / specNorm (G + Gᵀ)) • (G + Gᵀ)) ^ k‖ ≤ 1 := by
    calc _ ≤ ‖(1 / specNorm (G + Gᵀ)) • (G + Gᵀ)‖ ^ k := norm_pow_le' _ hk
      _ ≤ 1 := pow_le_one₀ (norm_nonneg _) hB
  have := walks_le ((1 / specNorm (G + Gᵀ)) • (G + Gᵀ)) k
  rw [walks_smul] at this
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc _ ≤ _ := this
    _ ≤ 1 * n := mul_le_mul_of_nonneg_right hBk hn
    _ = n := one_mul _
