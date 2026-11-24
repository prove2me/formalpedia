-- Prove2me | solution 1 for GlobalTheory.ClassFin.gram_minor_swap_columns
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:12:14.917035+00:00
-- url     : https://prove2.me/submissions/9d9a1981-5576-4427-b2ca-80f4c8a80381

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_GramMinorSwapAdjacentColumns
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
namespace GlobalTheory.ClassFin
private theorem exch_sum_split {N : ℕ} (p q : Fin N) (hq : (q : ℕ) = p + 1) (f : Fin N → ℝ)
    (hf : ∀ r, q < r → f r = 0) :
    ∑ r, f r = ∑ r ∈ Finset.univ.filter (· < p), f r + (f p + f q) := by
  have hpq : p ≠ q := fun e => by have := congrArg Fin.val e; omega
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· < p)]
  congr 1
  have hsub : ({p, q} : Finset (Fin N)) ⊆ Finset.univ.filter (fun r => ¬ r < p) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Fin.le_def]
    rcases hx with rfl | rfl <;> omega
  rw [← Finset.sum_subset hsub, Finset.sum_pair hpq]
  intro x hx hx'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Fin.le_def] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx'
  apply hf
  rw [Fin.lt_def]
  have h1 : (x : ℕ) ≠ p := fun e => hx'.1 (Fin.ext e)
  have h2 : (x : ℕ) ≠ q := fun e => hx'.2 (Fin.ext e)
  omega
private theorem det_updateRow_last_single_eq_mul_det_submatrix {m : ℕ} (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (x : ℝ) :
    (X.updateRow (Fin.last m) (Pi.single (Fin.last m) x)).det =
      x * (X.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row _ (Fin.last m), Finset.sum_eq_single (Fin.last m)]
  · have hsub : (X.updateRow (Fin.last m) (Pi.single (Fin.last m) x)).submatrix
        (Fin.last m).succAbove (Fin.last m).succAbove = X.submatrix Fin.castSucc Fin.castSucc := by
      ext i j
      simp only [Matrix.submatrix_apply, Fin.succAbove_last]
      rw [Matrix.updateRow_ne (Fin.castSucc_lt_last i).ne]
    rw [hsub, Matrix.updateRow_self, Pi.single_eq_same, Fin.val_last, Even.neg_one_pow ⟨m, rfl⟩, one_mul]
  · intro j _ hj
    rw [Matrix.updateRow_self, Pi.single_eq_of_ne hj, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
end GlobalTheory.ClassFin
end

set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin
namespace GlobalTheory.ClassFin
theorem _root_.solution : ∀ (N : ℕ) (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n g g' : Matrix (Fin N) (Fin N) ℝ) (p q : Fin N), kᵀ * k = 1 → (∀ i, n i i = 1) → (∀ i j, j < i → n i j = 0) → (q : ℕ) = p + 1 → g = k * diagonal a * n → g' = g.submatrix id (Equiv.swap p q) → (∀ (j : ℕ) (h : j ≤ N), j ≠ q → ((g'ᵀ * g').submatrix (Fin.castLE h) (Fin.castLE h)).det = ((gᵀ * g).submatrix (Fin.castLE h) (Fin.castLE h)).det) ∧ ∀ h : (q : ℕ) ≤ N, ((g'ᵀ * g').submatrix (Fin.castLE h) (Fin.castLE h)).det = (∏ l ∈ Finset.univ.filter (· < p), a l ^ 2) * (a q ^ 2 + n p q ^ 2 * a p ^ 2) := by
  intro N k a n g g' p q hk hn1 hn0 hq hg hg'

  have hG : gᵀ * g = (diagonal a * n)ᵀ * (diagonal a * n) := by
    rw [hg]
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc kᵀ k, hk, Matrix.one_mul]
  have hG' : g'ᵀ * g' = (gᵀ * g).submatrix (Equiv.swap p q) (Equiv.swap p q) := by
    rw [hg']
    ext i j
    simp [Matrix.mul_apply]
  rw [hG', hG]
  set M : Matrix (Fin N) (Fin N) ℝ := diagonal a * n with hM
  have hMe : ∀ i j, M i j = a i * n i j := fun i j => by simp [hM, Matrix.diagonal_mul]
  have hMl : ∀ i j, j < i → M i j = 0 := fun i j h => by rw [hMe, hn0 i j h, mul_zero]
  have hMd : ∀ i, M i i = a i := fun i => by rw [hMe, hn1, mul_one]
  refine ⟨fun j hj hjq => ?_, fun h => ?_⟩
  · by_cases hjp : j ≤ (p : ℕ)
    ·
      congr 1
      have hfix : ∀ z : Fin j, Equiv.swap p q (Fin.castLE hj z) = Fin.castLE hj z := by
        intro z
        have hz := z.isLt
        apply Equiv.swap_apply_of_ne_of_ne
        · intro e
          have := congrArg Fin.val e
          simp only [Fin.coe_castLE] at this
          omega
        · intro e
          have := congrArg Fin.val e
          simp only [Fin.coe_castLE] at this
          omega
      ext x y
      simp only [Matrix.submatrix_apply, hfix]
    ·
      have hpj : (p : ℕ) < j := by omega
      have hqj : (q : ℕ) < j := by omega
      have e1 : Fin.castLE hj ⟨p, hpj⟩ = p := Fin.ext rfl
      have e2 : Fin.castLE hj ⟨q, hqj⟩ = q := Fin.ext rfl
      have hs : ∀ z : Fin j, Equiv.swap p q (Fin.castLE hj z) =
          Fin.castLE hj (Equiv.swap ⟨p, hpj⟩ ⟨q, hqj⟩ z) := by
        intro z
        have := (Fin.castLE_injective hj).swap_apply ⟨p, hpj⟩ ⟨q, hqj⟩ z
        rwa [e1, e2] at this
      have hsub : ((Mᵀ * M).submatrix (Equiv.swap p q) (Equiv.swap p q)).submatrix (Fin.castLE hj)
          (Fin.castLE hj) = ((Mᵀ * M).submatrix (Fin.castLE hj) (Fin.castLE hj)).submatrix
          (Equiv.swap (⟨p, hpj⟩ : Fin j) ⟨q, hqj⟩) (Equiv.swap (⟨p, hpj⟩ : Fin j) ⟨q, hqj⟩) := by
        ext x y
        simp only [Matrix.submatrix_apply, hs]
      rw [hsub, Matrix.det_submatrix_equiv_self]
  · obtain ⟨p, hp⟩ := p
    obtain ⟨q, hqN⟩ := q
    change q = p + 1 at hq
    subst hq
    have h' : p + 1 ≤ N := h
    set P : Fin N := ⟨p, hp⟩ with hP
    set Q : Fin N := ⟨p + 1, hqN⟩ with hQ
    set σ := Equiv.swap P Q with hσ
    set c : Fin (p + 1) → Fin N := Fin.castLE h' with hc
    show (((Mᵀ * M).submatrix σ σ).submatrix c c).det = _
    have hcl : c (Fin.last p) = P := Fin.ext rfl
    have hσc : ∀ s : Fin (p + 1), s ≠ Fin.last p → σ (c s) = c s := by
      intro s hs
      have h1 : (s : ℕ) < p := by
        have := s.isLt
        have : (s : ℕ) ≠ p := fun e => hs (Fin.ext e)
        omega
      apply Equiv.swap_apply_of_ne_of_ne
      · intro e
        have := congrArg Fin.val e
        change (s : ℕ) = p at this
        omega
      · intro e
        have := congrArg Fin.val e
        change (s : ℕ) = p + 1 at this
        omega
    have hσl : σ (c (Fin.last p)) = Q := by
      rw [hcl]
      exact Equiv.swap_apply_left P Q
    have hle : ∀ s, σ (c s) ≤ Q := by
      intro s
      by_cases hs : s = Fin.last p
      · rw [hs, hσl]
      · rw [hσc s hs, Fin.le_def]
        change (s : ℕ) ≤ p + 1
        have := s.isLt
        omega

    set B : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ := Matrix.of fun s i => M (c s) (σ (c i)) with hB
    have hBe : ∀ s i, B s i = M (c s) (σ (c i)) := fun s i => rfl
    set emb : Fin p ↪ Fin N :=
      ⟨fun i : Fin p => c i.castSucc, fun x y e => by simpa [Fin.ext_iff, hc] using e⟩ with hemb
    have hembx : ∀ x, emb x = c x.castSucc := fun x => rfl
    have hfilt : Finset.univ.filter (· < P) = (Finset.univ : Finset (Fin p)).map emb := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro hl
        exact ⟨⟨l, hl⟩, Fin.ext rfl⟩
      · rintro ⟨i, _, rfl⟩
        exact i.isLt

    have hX : ((Mᵀ * M).submatrix σ σ).submatrix c c =
        (Bᵀ * B).updateRow (Fin.last p) ((Bᵀ * B) (Fin.last p) + Pi.single (Fin.last p) (a Q ^ 2)) := by
      ext i j
      have hsum : (((Mᵀ * M).submatrix σ σ).submatrix c c) i j =
          (Bᵀ * B) i j + M Q (σ (c i)) * M Q (σ (c j)) := by
        simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, hBe]
        rw [exch_sum_split P Q rfl _ (fun r hr => by rw [hMl r _ (lt_of_le_of_lt (hle i) hr), zero_mul]),
          Fin.sum_univ_castSucc, hfilt, Finset.sum_map, hcl]
        simp only [hembx]
        ring
      rw [hsum]
      by_cases hi : i = Fin.last p
      · subst hi
        rw [Matrix.updateRow_self, Pi.add_apply]
        by_cases hj : j = Fin.last p
        · subst hj
          rw [hσl, hMd, Pi.single_eq_same]
          ring
        · rw [hσl, hσc j hj, hMl Q (c j) (Fin.lt_def.2 j.isLt), mul_zero, Pi.single_eq_of_ne hj]
      · rw [Matrix.updateRow_ne hi, hσc i hi, hMl Q (c i) (Fin.lt_def.2 i.isLt), zero_mul, add_zero]
    have hBT : B.BlockTriangular id := by
      intro s i hi
      have hil : i ≠ Fin.last p := fun e => by
        rw [e] at hi
        exact (not_lt.2 (Fin.le_last s)) hi
      rw [hBe, hσc i hil]
      exact hMl _ _ (Fin.lt_def.2 (Fin.lt_def.1 hi))
    have hdB : B.det = (∏ i : Fin p, a (c i.castSucc)) * (a P * n P Q) := by
      rw [Matrix.det_of_upperTriangular hBT, Fin.prod_univ_castSucc]
      congr 1
      · refine Finset.prod_congr rfl fun i _ => ?_
        rw [hBe, hσc _ (Fin.castSucc_lt_last i).ne, hMd]
      · rw [hBe, hσl, hcl, hMe]
    have hminor : (Bᵀ * B).submatrix Fin.castSucc Fin.castSucc =
        (B.submatrix Fin.castSucc Fin.castSucc)ᵀ * B.submatrix Fin.castSucc Fin.castSucc := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply]
      rw [Fin.sum_univ_castSucc]
      have hz : B (Fin.last p) i.castSucc = 0 := by
        rw [hBe, hσc _ (Fin.castSucc_lt_last i).ne, hcl]
        exact hMl _ _ (Fin.lt_def.2 (Fin.lt_def.1 (Fin.castSucc_lt_last i)))
      rw [hz, zero_mul, add_zero]
    have hBT' : (B.submatrix Fin.castSucc Fin.castSucc).BlockTriangular id := by
      intro s i hi
      exact hBT (Fin.castSucc_lt_castSucc_iff.2 hi)
    have hdB' : (B.submatrix Fin.castSucc Fin.castSucc).det = ∏ i : Fin p, a (c i.castSucc) := by
      rw [Matrix.det_of_upperTriangular hBT']
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Matrix.submatrix_apply, hBe, hσc _ (Fin.castSucc_lt_last i).ne, hMd]
    have hprod : ∏ l ∈ Finset.univ.filter (· < P), a l ^ 2 = (∏ i : Fin p, a (c i.castSucc)) ^ 2 := by
      rw [hfilt, Finset.prod_map, ← Finset.prod_pow]
      simp only [hembx]
    rw [hX, Matrix.det_updateRow_add, Matrix.updateRow_eq_self, det_updateRow_last_single_eq_mul_det_submatrix, hminor,
      Matrix.det_mul, Matrix.det_transpose, Matrix.det_mul, Matrix.det_transpose, hdB, hdB', hprod]
    ring
end GlobalTheory.ClassFin
