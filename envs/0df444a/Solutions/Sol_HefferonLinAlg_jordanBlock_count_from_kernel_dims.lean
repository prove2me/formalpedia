-- Prove2me | solution 1 for HefferonLinAlg.jordanBlock_count_from_kernel_dims
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-08-07T14:52:12.216654+00:00
-- url     : https://prove2.me/submissions/f7ab7f8c-bb56-463f-9f14-69f0c343d545

import Mathlib
import Definitions.Def_HefferonLinAlg_jordan

open Matrix
open HefferonLinAlg

universe u v

section BlockDiag

variable {K : Type u} [Field K] {o : Type v} [Fintype o] [DecidableEq o]
  {m' : o → Type v} [∀ i, Fintype (m' i)] [∀ i, DecidableEq (m' i)]

private theorem blockDiagonal'_mulVec_apply (M : ∀ i, Matrix (m' i) (m' i) K)
    (v : (Σ i, m' i) → K) (i : o) (x : m' i) :
    (Matrix.blockDiagonal' M *ᵥ v) ⟨i, x⟩ = (M i *ᵥ fun y => v ⟨i, y⟩) x := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro y _
    rw [Matrix.blockDiagonal'_apply_eq]
  · intro j _ hj
    apply Finset.sum_eq_zero
    intro y _
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hj), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The kernel of a block-diagonal matrix is the product of the kernels of the blocks. -/
private def kerBlockDiagonal'Equiv (M : ∀ i, Matrix (m' i) (m' i) K) :
    LinearMap.ker (Matrix.toLin' (Matrix.blockDiagonal' M)) ≃ₗ[K]
      (∀ i, LinearMap.ker (Matrix.toLin' (M i))) where
  toFun v i := ⟨fun y => (v : (Σ i, m' i) → K) ⟨i, y⟩, by
    have hv : Matrix.blockDiagonal' M *ᵥ (v : (Σ i, m' i) → K) = 0 := by
      have := v.2
      rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at this
    simp only [LinearMap.mem_ker, Matrix.toLin'_apply]
    funext x
    rw [← blockDiagonal'_mulVec_apply M (v : (Σ i, m' i) → K) i x, hv]
    rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun w := ⟨fun p => (w p.1 : m' p.1 → K) p.2, by
    simp only [LinearMap.mem_ker, Matrix.toLin'_apply]
    funext p
    obtain ⟨i, x⟩ := p
    rw [blockDiagonal'_mulVec_apply]
    have : M i *ᵥ (w i : m' i → K) = 0 := by
      have := (w i).2
      rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at this
    rw [this]
    rfl⟩
  left_inv v := by ext p; cases p; rfl
  right_inv w := by ext i x; rfl

private theorem finrank_ker_blockDiagonal' (M : ∀ i, Matrix (m' i) (m' i) K) :
    Module.finrank K (LinearMap.ker (Matrix.toLin' (Matrix.blockDiagonal' M)))
      = ∑ i, Module.finrank K (LinearMap.ker (Matrix.toLin' (M i))) := by
  rw [(kerBlockDiagonal'Equiv M).finrank_eq, Module.finrank_pi_fintype]

end BlockDiag

section RankKer

variable {K : Type u} [Field K] {ι : Type v} [Fintype ι] [DecidableEq ι]

private theorem finrank_ker_add_rank (A : Matrix ι ι K) :
    Module.finrank K (LinearMap.ker (Matrix.toLin' A)) + A.rank = Fintype.card ι := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin A)
  rw [Module.finrank_pi] at h
  rw [Matrix.toLin'_apply', Matrix.rank]
  omega

private theorem finrank_ker_eq_of_rank_eq {κ : Type v} [Fintype κ] [DecidableEq κ]
    {A : Matrix ι ι K} {B : Matrix κ κ K}
    (hcard : Fintype.card ι = Fintype.card κ) (h : A.rank = B.rank) :
    Module.finrank K (LinearMap.ker (Matrix.toLin' A))
      = Module.finrank K (LinearMap.ker (Matrix.toLin' B)) := by
  have hA := finrank_ker_add_rank A
  have hB := finrank_ker_add_rank B
  omega

private theorem finrank_ker_conj (A P : Matrix ι ι K) (hP : IsUnit P.det) :
    Module.finrank K (LinearMap.ker (Matrix.toLin' (P⁻¹ * A * P)))
      = Module.finrank K (LinearMap.ker (Matrix.toLin' A)) := by
  have hPinv : IsUnit (P⁻¹).det := Matrix.isUnit_nonsing_inv_det P hP
  refine finrank_ker_eq_of_rank_eq rfl ?_
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hP,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hPinv]

private theorem finrank_ker_reindex {κ : Type v} [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (A : Matrix ι ι K) :
    Module.finrank K (LinearMap.ker (Matrix.toLin' (Matrix.reindex e e A)))
      = Module.finrank K (LinearMap.ker (Matrix.toLin' A)) :=
  finrank_ker_eq_of_rank_eq (Fintype.card_congr e.symm) (Matrix.rank_reindex e e A)

end RankKer

section JordanBlockKer

variable {K : Type u} [Field K]

private theorem jordanBlock_sub_smul_one (m : ℕ) (lam mu : K) :
    jordanBlock m lam - mu • (1 : Matrix (Fin m) (Fin m) K) = jordanBlock m (lam - mu) := by
  ext i j
  by_cases h : i = j <;> simp [h]

private theorem jordanBlock_zero_apply (m : ℕ) (i j : Fin m) :
    jordanBlock m (0 : K) i j = if (i : ℕ) = (j : ℕ) + 1 then 1 else 0 := by
  by_cases h : i = j
  · subst h; simp
  · simp [h]

private theorem jordanBlock_zero_pow_apply (m r : ℕ) (i j : Fin m) :
    ((jordanBlock m (0 : K)) ^ r) i j = if (i : ℕ) = (j : ℕ) + r then 1 else 0 := by
  induction r generalizing i j with
  | zero => simp [Matrix.one_apply, Fin.ext_iff]
  | succ r ih =>
      rw [pow_succ', Matrix.mul_apply]
      simp only [jordanBlock_zero_apply, ih]
      by_cases hi : (i : ℕ) = (j : ℕ) + (r + 1)
      · have hlt : (j : ℕ) + r < m := by omega
        rw [Finset.sum_eq_single (⟨(j : ℕ) + r, hlt⟩ : Fin m)]
        · simp [hi]
          omega
        · intro l _ hl
          by_cases h1 : (i : ℕ) = (l : ℕ) + 1
          · exfalso
            apply hl
            apply Fin.ext
            simp only
            omega
          · simp [h1]
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [if_neg hi]
        apply Finset.sum_eq_zero
        intro l _
        by_cases h1 : (i : ℕ) = (l : ℕ) + 1
        · by_cases h2 : (l : ℕ) = (j : ℕ) + r
          · omega
          · simp [h2]
        · simp [h1]

/-- The kernel of the `r`-th power of the nilpotent Jordan block is spanned by the last
`min m r` coordinate vectors. -/
private theorem finrank_ker_jordanBlock_zero_pow (m r : ℕ) :
    Module.finrank K (LinearMap.ker (Matrix.toLin' ((jordanBlock m (0 : K)) ^ r)))
      = min m r := by
  classical
  have hle : m - r ≤ m := Nat.sub_le m r
  set f : Fin (m - r) → Fin m := Fin.castLE hle with hf
  have hker : LinearMap.ker (Matrix.toLin' ((jordanBlock m (0 : K)) ^ r))
      = LinearMap.ker (LinearMap.funLeft K K f) := by
    ext v
    simp only [LinearMap.mem_ker, Matrix.toLin'_apply]
    constructor
    · intro h
      funext j
      have hlt : (j : ℕ) + r < m := by
        have := j.2; omega
      have := congrFun h (⟨(j : ℕ) + r, hlt⟩ : Fin m)
      rw [Matrix.mulVec, dotProduct] at this
      simp only [jordanBlock_zero_pow_apply] at this
      rw [Finset.sum_eq_single (f j)] at this
      · simpa [hf, Fin.castLE] using this
      · intro l _ hl
        have : ¬ ((j : ℕ) + r = (l : ℕ) + r) := by
          intro hc
          exact hl (Fin.ext (by simp [hf, Fin.castLE]; omega))
        rw [if_neg this, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro h
      funext i
      rw [Matrix.mulVec, dotProduct]
      simp only [jordanBlock_zero_pow_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hc : (i : ℕ) = (l : ℕ) + r
      · have hlt : (l : ℕ) + r < m := by have := i.2; omega
        have hl' : (l : ℕ) < m - r := by omega
        have := congrFun h (⟨(l : ℕ), hl'⟩ : Fin (m - r))
        simp only [LinearMap.funLeft_apply, Pi.zero_apply] at this
        have hfl : f ⟨(l : ℕ), hl'⟩ = l := Fin.ext (by simp [hf])
        rw [hfl] at this
        simp [hc, this]
      · simp [hc]
  rw [hker]
  have hsurj : Function.Surjective (LinearMap.funLeft K K f) :=
    LinearMap.funLeft_surjective_of_injective K K f (Fin.castLE_injective hle)
  have h1 := LinearMap.finrank_range_add_finrank_ker (LinearMap.funLeft K K f)
  rw [LinearMap.range_eq_top.mpr hsurj] at h1
  simp only [finrank_top, Module.finrank_pi, Fintype.card_fin] at h1
  omega

private theorem finrank_ker_jordanBlock_pow_self (m r : ℕ) (mu : K) :
    Module.finrank K
        (LinearMap.ker (Matrix.toLin'
          ((jordanBlock m mu - mu • (1 : Matrix (Fin m) (Fin m) K)) ^ r)))
      = min m r := by
  rw [jordanBlock_sub_smul_one, sub_self]
  exact finrank_ker_jordanBlock_zero_pow m r

private theorem finrank_ker_jordanBlock_pow_of_ne (m r : ℕ) (lam mu : K) (h : lam ≠ mu) :
    Module.finrank K
        (LinearMap.ker (Matrix.toLin'
          ((jordanBlock m lam - mu • (1 : Matrix (Fin m) (Fin m) K)) ^ r)))
      = 0 := by
  rw [jordanBlock_sub_smul_one]
  have hne : lam - mu ≠ 0 := sub_ne_zero.mpr h
  have hdet : (jordanBlock m (lam - mu)).det = (lam - mu) ^ m := by
    rw [Matrix.det_of_lowerTriangular]
    · simp
    · intro i j hij
      have hv : (i : ℕ) < (j : ℕ) := hij
      have h1 : (i : ℕ) ≠ (j : ℕ) + 1 := by omega
      have h0 : ¬ (i = j) := by
        intro hc; rw [hc] at hv; omega
      simp [h0, h1]
  have hunit : IsUnit (jordanBlock m (lam - mu)) := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet]
    exact (pow_ne_zero m hne).isUnit
  have hpow : IsUnit ((jordanBlock m (lam - mu)) ^ r) := hunit.pow r
  have hrank := Matrix.rank_of_isUnit _ hpow
  have h2 := finrank_ker_add_rank ((jordanBlock m (lam - mu)) ^ r)
  rw [hrank] at h2
  simp only [Fintype.card_fin] at h2
  omega

end JordanBlockKer

section Assemble

private theorem inv_conj_pow {K : Type u} [Field K] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (X P : Matrix ι ι K) (hP : IsUnit P.det) (s : ℕ) :
    (P⁻¹ * X * P) ^ s = P⁻¹ * X ^ s * P := by
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  have hPP' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  induction s with
  | zero => simp [hPP]
  | succ s ih =>
      calc (P⁻¹ * X * P) ^ (s + 1)
          = (P⁻¹ * X ^ s * P) * (P⁻¹ * X * P) := by rw [pow_succ, ih]
        _ = P⁻¹ * X ^ s * (P * P⁻¹) * X * P := by simp [mul_assoc]
        _ = P⁻¹ * X ^ (s + 1) * P := by rw [hPP']; simp [pow_succ, mul_assoc]

private theorem kerDim_eq_sum {n k : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {sz : Fin k → ℕ}
    {lam : Fin k → ℂ} (h : IsJordanFormOf A sz lam) (mu : ℂ) (s : ℕ) :
    kerDim A mu s = ∑ i, (if lam i = mu then min (sz i) s else 0) := by
  classical
  obtain ⟨hpos, e, P, hP, hPeq⟩ := h
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  have h1 : kerDim A mu s
      = Module.finrank ℂ (LinearMap.ker (Matrix.toLin' ((P⁻¹ * (A - mu • 1) * P) ^ s))) := by
    rw [inv_conj_pow _ _ hP, finrank_ker_conj _ _ hP]
    rfl
  have h2 : P⁻¹ * (A - mu • (1 : Matrix (Fin n) (Fin n) ℂ)) * P
      = Matrix.reindex e.symm e.symm (jordanMatrix sz lam) - mu • 1 := by
    rw [← hPeq, Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    simp [hPP]
  have hone : Matrix.reindexAlgEquiv ℂ ℂ e.symm
      (mu • (1 : Matrix (jordanIndex sz) (jordanIndex sz) ℂ))
      = mu • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [map_smul, map_one]
  have h3 : (Matrix.reindex e.symm e.symm (jordanMatrix sz lam)
        - mu • (1 : Matrix (Fin n) (Fin n) ℂ)) ^ s
      = Matrix.reindex e.symm e.symm ((jordanMatrix sz lam - mu • 1) ^ s) := by
    conv_lhs => rw [← Matrix.reindexAlgEquiv_apply ℂ ℂ e.symm (jordanMatrix sz lam), ← hone]
    rw [← map_sub, ← map_pow, Matrix.reindexAlgEquiv_apply]
  have hblk : Matrix.blockDiagonal'
        (fun i => jordanBlock (sz i) (lam i) - mu • (1 : Matrix (Fin (sz i)) (Fin (sz i)) ℂ))
      = jordanMatrix sz lam - mu • 1 := by
    have hfun : (fun i => jordanBlock (sz i) (lam i)
          - mu • (1 : Matrix (Fin (sz i)) (Fin (sz i)) ℂ))
        = (fun i => jordanBlock (sz i) (lam i))
          - (fun i => mu • (1 : Matrix (Fin (sz i)) (Fin (sz i)) ℂ)) := rfl
    have hsm : (fun i => mu • (1 : Matrix (Fin (sz i)) (Fin (sz i)) ℂ))
        = mu • (fun i => (1 : Matrix (Fin (sz i)) (Fin (sz i)) ℂ)) := rfl
    have hone1 : (fun i => (1 : Matrix (Fin (sz i)) (Fin (sz i)) ℂ)) = 1 := rfl
    rw [hfun, Matrix.blockDiagonal'_sub, hsm, Matrix.blockDiagonal'_smul, hone1,
      Matrix.blockDiagonal'_one]
    rfl
  have h4 : (jordanMatrix sz lam - mu • (1 : Matrix (jordanIndex sz) (jordanIndex sz) ℂ)) ^ s
      = Matrix.blockDiagonal' (fun i => (jordanBlock (sz i) (lam i) - mu • 1) ^ s) := by
    rw [← hblk, ← Matrix.blockDiagonal'_pow]
    rfl
  rw [h1, h2, h3, finrank_ker_reindex, h4, finrank_ker_blockDiagonal']
  apply Finset.sum_congr rfl
  intro i _
  by_cases hl : lam i = mu
  · rw [if_pos hl, hl]
    exact finrank_ker_jordanBlock_pow_self (sz i) s mu
  · rw [if_neg hl]
    exact finrank_ker_jordanBlock_pow_of_ne (sz i) s (lam i) mu hl

theorem solution
    {n k : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {sz : Fin k → ℕ} {lam : Fin k → ℂ}
    (h : IsJordanFormOf A sz lam) (mu : ℂ) (r : ℕ) :
    (Finset.univ.filter fun i => sz i = r + 1 ∧ lam i = mu).card
        + kerDim A mu r + kerDim A mu (r + 2)
      = 2 * kerDim A mu (r + 1) := by
  classical
  rw [kerDim_eq_sum h, kerDim_eq_sum h, kerDim_eq_sum h, Finset.card_filter,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hl : lam i = mu
  · by_cases hs : sz i = r + 1
    · rw [if_pos ⟨hs, hl⟩, if_pos hl, if_pos hl, if_pos hl, hs]
      omega
    · rw [if_neg (fun hc => hs hc.1), if_pos hl, if_pos hl, if_pos hl]
      omega
  · rw [if_neg (fun hc => hl hc.2), if_neg hl, if_neg hl, if_neg hl]
    omega

end Assemble
