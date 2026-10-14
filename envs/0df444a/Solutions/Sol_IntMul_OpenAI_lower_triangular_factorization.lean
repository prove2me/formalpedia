-- Prove2me | solution 1 for IntMul.OpenAI.lower_triangular_factorization
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-12T13:50:31.221467+00:00
-- url     : https://prove2.me/submissions/c65cb1b0-aef1-4c2e-9f25-1e24254a141c

import Mathlib

open Matrix Finset

namespace BruhatAux

variable {K : Type*} [Field K] {m : ℕ}

/-- Lower triangular with nonzero diagonal. -/
def LowerND (M : Matrix (Fin m) (Fin m) K) : Prop :=
  (∀ i j, i < j → M i j = 0) ∧ ∀ i, M i i ≠ 0

lemma lowerND_one : LowerND (1 : Matrix (Fin m) (Fin m) K) :=
  ⟨fun i j h => by simp [one_apply, h.ne], fun i => by simp⟩

lemma lowerND_mul {M N : Matrix (Fin m) (Fin m) K} (hM : LowerND M) (hN : LowerND N) :
    LowerND (M * N) := by
  have diag : ∀ i, (M * N) i i = M i i * N i i := by
    intro i
    rw [mul_apply, Finset.sum_eq_single i]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hN.1 k i h, mul_zero]
      · rw [hM.1 i k h, zero_mul]
    · simp
  refine ⟨fun i j hij => ?_, fun i => by rw [diag]; exact mul_ne_zero (hM.2 i) (hN.2 i)⟩
  rw [mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge i k with h | h
  · rw [hM.1 i k h, zero_mul]
  · rw [hN.1 k j (lt_of_le_of_lt h hij), mul_zero]

lemma isLower_of (M : Matrix (Fin m) (Fin m) K) (h : LowerND M) : M.IsLowerTriangular :=
  fun i j hij => h.1 i j hij

lemma det_ne_zero_of (M : Matrix (Fin m) (Fin m) K) (h : LowerND M) : M.det ≠ 0 := by
  rw [det_of_isLowerTriangular M (isLower_of M h)]
  exact Finset.prod_ne_zero_iff.2 fun i _ => h.2 i

lemma lowerND_inv (M : Matrix (Fin m) (Fin m) K) (h : LowerND M) : LowerND M⁻¹ := by
  have hd : IsUnit M.det := isUnit_iff_ne_zero.2 (det_ne_zero_of M h)
  have : Invertible M := invertibleOfIsUnitDet M hd
  have hl : M⁻¹.IsLowerTriangular := blockTriangular_inv_of_blockTriangular (isLower_of M h)
  refine ⟨fun i j hij => hl hij, fun i => ?_⟩
  -- diagonal of M * M⁻¹ = 1
  have h1 : (M * M⁻¹) i i = 1 := by rw [mul_inv_of_invertible]; simp
  have h2 : (M * M⁻¹) i i = M i i * M⁻¹ i i := by
    rw [mul_apply, Finset.sum_eq_single i]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hk | hk
      · rw [hl hk, mul_zero]
      · rw [h.1 i k hk, zero_mul]
    · simp
  intro h0
  rw [h2, h0, mul_zero] at h1
  exact zero_ne_one h1

/-- Rows with index `< k` are clean: zero, or a single `1` whose column is otherwise zero. -/
def Clean (B : Matrix (Fin m) (Fin m) K) (k : ℕ) : Prop :=
  ∀ i : Fin m, i.val < k → (∀ j, B i j = 0) ∨
    ∃ j, B i j = 1 ∧ (∀ j', j' ≠ j → B i j' = 0) ∧ ∀ i', i' ≠ i → B i' j = 0

lemma clean_zero (B : Matrix (Fin m) (Fin m) K) : Clean B 0 := fun i h => absurd h (Nat.not_lt_zero _)

/-- In a clean row `r < k`, the entry in any column `j` where row `k'` (with `k' ≥ k`) is nonzero vanishes. -/
lemma clean_col_zero {B : Matrix (Fin m) (Fin m) K} {k : ℕ} (hB : Clean B k) (r k' : Fin m)
    (hr : r.val < k) (hk' : k ≤ k'.val) (j : Fin m) (hj : B k' j ≠ 0) : B r j = 0 := by
  rcases hB r hr with h | ⟨σ, -, hrow, hcol⟩
  · exact h j
  · by_cases hσ : j = σ
    · subst hσ
      exact absurd (hcol k' (fun h => by subst h; omega)) hj
    · exact hrow j hσ

lemma step (B : Matrix (Fin m) (Fin m) K) (k : Fin m) (hB : Clean B k.val) :
    ∃ L R : Matrix (Fin m) (Fin m) K, LowerND L ∧ LowerND R ∧ Clean (L * B * R) (k.val + 1) := by
  classical
  by_cases hz : ∀ j, B k j = 0
  · refine ⟨1, 1, lowerND_one, lowerND_one, ?_⟩
    simp only [Matrix.one_mul, Matrix.mul_one]
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
    · exact hB i h
    · left; have : i = k := Fin.ext h; subst this; exact hz
  push Not at hz
  have hne : (univ.filter fun j => B k j ≠ 0).Nonempty := by
    obtain ⟨j, hj⟩ := hz; exact ⟨j, by simp [hj]⟩
  set j0 := (univ.filter fun j => B k j ≠ 0).max' hne with hj0def
  have hj0 : B k j0 ≠ 0 := by
    have := Finset.max'_mem _ hne
    simpa using this
  have hright : ∀ j, j0 < j → B k j = 0 := by
    intro j hj
    by_contra h
    have : j ≤ j0 := Finset.le_max' _ j (by simp [h])
    exact absurd hj (not_lt.2 this)
  set b := B k j0 with hb
  -- column operations
  set N : Matrix (Fin m) (Fin m) K := Matrix.of fun a c => if a = j0 ∧ c < j0 then -(B k c / b) else 0
  set R1 : Matrix (Fin m) (Fin m) K := 1 + N
  have hR1 : LowerND R1 := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · simp only [R1, N, Matrix.add_apply, one_apply, of_apply, hij.ne, if_false, zero_add]
      rw [if_neg]; rintro ⟨rfl, h⟩; exact absurd (hij.trans h) (lt_irrefl _)
    · simp only [R1, N, Matrix.add_apply, of_apply, one_apply_eq]
      rw [if_neg (by rintro ⟨rfl, h⟩; exact lt_irrefl _ h)]; simp
  set B1 := B * R1 with hB1def
  have hB1 : ∀ r c, B1 r c = B r c + (if c < j0 then -(B k c / b) * B r j0 else 0) := by
    intro r c
    simp only [B1, R1, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
    congr 1
    rw [mul_apply, Finset.sum_eq_single j0]
    · simp only [N, of_apply, true_and]
      split_ifs <;> ring
    · intro a _ ha; simp [N, ha]
    · simp
  have hB1k : ∀ c, B1 k c = if c = j0 then b else 0 := by
    intro c
    rw [hB1]
    rcases lt_trichotomy c j0 with h | h | h
    · rw [if_pos h, if_neg h.ne]; field_simp; ring
    · subst h; simp [hb]
    · rw [if_neg (not_lt.2 h.le), if_neg h.ne', hright c h, add_zero]
  -- row operations
  set M : Matrix (Fin m) (Fin m) K := Matrix.of fun r a => if a = k ∧ k < r then -(B1 r j0 / b) else 0
  set L1 : Matrix (Fin m) (Fin m) K := 1 + M
  have hL1 : LowerND L1 := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · simp only [L1, M, Matrix.add_apply, one_apply, of_apply, hij.ne, if_false, zero_add]
      rw [if_neg]; rintro ⟨rfl, h⟩; exact absurd (hij.trans h) (lt_irrefl _)
    · simp only [L1, M, Matrix.add_apply, of_apply, one_apply_eq]
      rw [if_neg (by rintro ⟨rfl, h⟩; exact lt_irrefl _ h)]; simp
  set B2 := L1 * B1 with hB2def
  have hB2 : ∀ r c, B2 r c = B1 r c + (if k < r then -(B1 r j0 / b) * B1 k c else 0) := by
    intro r c
    simp only [B2, L1, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply]
    congr 1
    rw [mul_apply, Finset.sum_eq_single k]
    · simp only [M, of_apply, true_and]
      split_ifs <;> ring
    · intro a _ ha; simp [M, ha]
    · simp
  -- scaling
  set D : Matrix (Fin m) (Fin m) K := diagonal fun i => if i = k then b⁻¹ else 1
  have hD : LowerND D := by
    refine ⟨fun i j hij => by simp [D, diagonal_apply, hij.ne], fun i => ?_⟩
    simp only [D, diagonal_apply_eq]
    split_ifs
    · exact inv_ne_zero hj0
    · exact one_ne_zero
  refine ⟨D * L1, R1, lowerND_mul hD hL1, hR1, ?_⟩
  have hfin : D * L1 * B * R1 = D * B2 := by
    simp only [B2, B1, Matrix.mul_assoc]
  rw [hfin]
  have hDB : ∀ r c, (D * B2) r c = (if r = k then b⁻¹ else 1) * B2 r c := by
    intro r c; simp [D, diagonal_mul]
  -- clean rows below k are untouched
  have hold : ∀ r : Fin m, r.val < k.val → ∀ c, (D * B2) r c = B r c := by
    intro r hr c
    have hrk : r ≠ k := fun h => by subst h; omega
    have hkr : ¬ k < r := fun h => by rw [Fin.lt_def] at h; omega
    have hrj0 : B r j0 = 0 := clean_col_zero hB r k hr le_rfl j0 hj0
    rw [hDB, if_neg hrk, one_mul, hB2, if_neg hkr, add_zero, hB1, hrj0]
    simp
  intro i hi
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
  · rcases hB i hi with h | ⟨σ, h1, hrow, hcol⟩
    · left; intro j; rw [hold i hi, h]
    · right
      refine ⟨σ, by rw [hold i hi, h1], fun j hj => by rw [hold i hi, hrow j hj], fun i' hi' => ?_⟩
      have hσj0 : σ ≠ j0 := by
        rintro rfl; exact hj0 (hcol k (fun h => by subst h; omega))
      have hkσ : B k σ = 0 := hcol k (fun h => by subst h; omega)
      rw [hDB, hB2, hB1k, if_neg hσj0, mul_zero]
      simp only [ite_self, add_zero]
      rw [hB1, hcol i' hi', hkσ]
      simp
  · have hik : i = k := Fin.ext hi
    subst hik
    right
    refine ⟨j0, ?_, fun j hj => ?_, fun i' hi' => ?_⟩
    · rw [hDB, if_pos rfl, hB2, if_neg (lt_irrefl _), add_zero, hB1k, if_pos rfl]
      exact inv_mul_cancel₀ hj0
    · rw [hDB, hB2, if_neg (lt_irrefl _), add_zero, hB1k, if_neg hj, mul_zero]
    · rw [hDB, if_neg hi', hB2, hB1k, if_pos rfl, one_mul]
      rcases lt_trichotomy i' i with h | h | h
      · rw [if_neg (not_lt.2 h.le), add_zero]
        have := hold i' h j0
        rw [hDB, if_neg hi', one_mul, hB2, if_neg (not_lt.2 h.le), add_zero] at this
        rw [this]
        exact clean_col_zero hB i' i h le_rfl j0 hj0
      · exact absurd h hi'
      · rw [if_pos h]; field_simp; ring

lemma reduce (A : Matrix (Fin m) (Fin m) K) :
    ∀ k ≤ m, ∃ L R : Matrix (Fin m) (Fin m) K, LowerND L ∧ LowerND R ∧ Clean (L * A * R) k := by
  intro k
  induction k with
  | zero => intro _; exact ⟨1, 1, lowerND_one, lowerND_one, clean_zero _⟩
  | succ k ih =>
    intro hk
    obtain ⟨L, R, hL, hR, hc⟩ := ih (by omega)
    obtain ⟨L', R', hL', hR', hc'⟩ := step (L * A * R) ⟨k, by omega⟩ hc
    refine ⟨L' * L, R * R', lowerND_mul hL' hL, lowerND_mul hR hR', ?_⟩
    simpa [Matrix.mul_assoc] using hc'

end BruhatAux

open BruhatAux in
theorem solution {m : ℕ} {K : Type*} [Field K] [DecidableEq K] (A : Matrix (Fin m) (Fin m) K) :
    ∃ E₁ P E₂ : Matrix (Fin m) (Fin m) K,
      (∀ i j, i < j → E₁ i j = 0) ∧ (∀ i, E₁ i i ≠ 0) ∧
      (∀ i j, i < j → E₂ i j = 0) ∧ (∀ i, E₂ i i ≠ 0) ∧
      (∀ i j, P i j = 0 ∨ P i j = 1) ∧
      (∀ i j j', P i j = 1 → P i j' = 1 → j = j') ∧
      (∀ i i' j, P i j = 1 → P i' j = 1 → i = i') ∧
      (Finset.univ.filter fun x : Fin m × Fin m => P x.1 x.2 = 1).card = A.rank ∧
      A = E₁ * P * E₂ := by
  classical
  obtain ⟨L, R, hL, hR, hc⟩ := reduce A m le_rfl
  set P := L * A * R with hP
  have hLd := det_ne_zero_of L hL
  have hRd := det_ne_zero_of R hR
  have : Invertible L := invertibleOfIsUnitDet L (isUnit_iff_ne_zero.2 hLd)
  have : Invertible R := invertibleOfIsUnitDet R (isUnit_iff_ne_zero.2 hRd)
  have hA : A = L⁻¹ * P * R⁻¹ := by
    simp only [hP, Matrix.mul_assoc, inv_mul_cancel_left_of_invertible]
    rw [Matrix.mul_inv_of_invertible, Matrix.mul_one]
  have hrow : ∀ i, (∀ j, P i j = 0) ∨
      ∃ j, P i j = 1 ∧ (∀ j', j' ≠ j → P i j' = 0) ∧ ∀ i', i' ≠ i → P i' j = 0 :=
    fun i => hc i i.isLt
  have h01 : ∀ i j, P i j = 0 ∨ P i j = 1 := by
    intro i j
    rcases hrow i with h | ⟨σ, h1, hr, -⟩
    · exact Or.inl (h j)
    · by_cases hj : j = σ
      · subst hj; exact Or.inr h1
      · exact Or.inl (hr j hj)
  have hrowu : ∀ i j j', P i j = 1 → P i j' = 1 → j = j' := by
    intro i j j' h h'
    rcases hrow i with hz | ⟨σ, -, hr, -⟩
    · rw [hz j] at h; exact absurd h zero_ne_one
    · by_contra hne
      by_cases hj : j = σ
      · subst hj; rw [hr j' (Ne.symm hne)] at h'; exact zero_ne_one h'
      · rw [hr j hj] at h; exact zero_ne_one h
  have hcolu : ∀ i i' j, P i j = 1 → P i' j = 1 → i = i' := by
    intro i i' j h h'
    rcases hrow i with hz | ⟨σ, -, hr, hcl⟩
    · rw [hz j] at h; exact absurd h zero_ne_one
    · have hjσ : j = σ := by
        by_contra hj; rw [hr j hj] at h; exact zero_ne_one h
      subst hjσ
      by_contra hne
      rw [hcl i' (Ne.symm hne)] at h'; exact zero_ne_one h'
  -- rank count
  have hrankP : P.rank = A.rank := by
    rw [hP, rank_mul_eq_left_of_isUnit_det R _ (isUnit_iff_ne_zero.2 hRd),
      rank_mul_eq_right_of_isUnit_det L A (isUnit_iff_ne_zero.2 hLd)]
  have hPPt : P * Pᵀ = diagonal fun i => if ∃ j, P i j = 1 then (1 : K) else 0 := by
    ext i i'
    rw [mul_apply, diagonal_apply]
    simp only [transpose_apply]
    by_cases hii : i = i'
    · subst hii
      rw [if_pos rfl]
      split_ifs with hex
      · obtain ⟨j, hj⟩ := hex
        rw [Finset.sum_eq_single j]
        · rw [hj, one_mul]
        · intro j' _ hj'
          rcases h01 i j' with h | h
          · rw [h, zero_mul]
          · exact absurd (hrowu i j j' hj h).symm hj'
        · simp
      · push Not at hex
        refine Finset.sum_eq_zero fun j _ => ?_
        rcases h01 i j with h | h
        · rw [h, zero_mul]
        · exact absurd h (hex j)
    · rw [if_neg hii]
      refine Finset.sum_eq_zero fun j _ => ?_
      rcases h01 i j with h | h
      · rw [h, zero_mul]
      rcases h01 i' j with h' | h'
      · rw [h', mul_zero]
      · exact absurd (hcolu i i' j h h') hii
  have hPPtP : P * Pᵀ * P = P := by
    rw [hPPt]
    ext i j
    rw [diagonal_mul]
    split_ifs with hex
    · rw [one_mul]
    · push Not at hex
      rw [zero_mul]
      rcases h01 i j with h | h
      · exact h.symm
      · exact absurd h (hex j)
  have hrank1 : P.rank = (P * Pᵀ).rank := by
    apply le_antisymm
    · calc P.rank = (P * Pᵀ * P).rank := by rw [hPPtP]
        _ ≤ (P * Pᵀ).rank := rank_mul_le_left _ _
    · exact rank_mul_le_left _ _
  have hrank2 : (P * Pᵀ).rank = (univ.filter fun i => ∃ j, P i j = 1).card := by
    rw [hPPt, rank_diagonal, Fintype.card_subtype]
    congr 1
    ext i; simp
  have hcount : (univ.filter fun x : Fin m × Fin m => P x.1 x.2 = 1).card =
      (univ.filter fun i => ∃ j, P i j = 1).card := by
    refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
    · intro x hx; simp only [mem_filter, mem_univ, true_and] at hx ⊢; exact ⟨x.2, hx⟩
    · intro x hx y hy hxy
      simp only [mem_filter, mem_univ, true_and] at hx hy
      have h2 : x.2 = y.2 := hrowu x.1 x.2 y.2 hx (hxy ▸ hy)
      exact Prod.ext hxy h2
    · intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi
      obtain ⟨j, hj⟩ := hi
      exact ⟨(i, j), by simp [hj], rfl⟩
  have hLi := lowerND_inv L hL
  have hRi := lowerND_inv R hR
  exact ⟨L⁻¹, P, R⁻¹, hLi.1, hLi.2, hRi.1, hRi.2, h01, hrowu, hcolu,
    by rw [hcount, ← hrank2, ← hrank1, hrankP], hA⟩
