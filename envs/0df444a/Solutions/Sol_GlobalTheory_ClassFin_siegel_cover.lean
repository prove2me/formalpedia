-- Prove2me | solution 1 for GlobalTheory.ClassFin.siegel_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:53:31.390532+00:00
-- url     : https://prove2.me/submissions/e6877679-45f4-4ab4-819d-ff447e0614a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsHermiteReducedLatticeBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SiegelCover
import Theorems.Thm_GlobalTheory_ClassFin_HermiteReduction_exists_reduced

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
open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma le_two_pow_mul_of_consecutive_le {N : ℕ} (a : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (h : ∀ p q : Fin N, (q : ℕ) = p + 1 → a p ≤ 2 * a q) (i j : Fin N) (hij : i < j) :
    a i ≤ 2 ^ N * a j := by
  have key : ∀ d : ℕ, ∀ i j : Fin N, (j : ℕ) = i + d → a i ≤ 2 ^ d * a j := by
    intro d
    induction d with
    | zero =>
      intro i j hij
      have : i = j := Fin.ext (by simpa using hij.symm)
      subst this
      simp
    | succ d ih =>
      intro i j hij
      have hm : (i : ℕ) + d < N := by have := j.isLt; omega
      have h1 := ih i ⟨i + d, hm⟩ rfl
      have h2 := h ⟨i + d, hm⟩ j (by simp only; omega)
      calc a i ≤ 2 ^ d * a ⟨i + d, hm⟩ := h1
        _ ≤ 2 ^ d * (2 * a j) := by gcongr
        _ = 2 ^ (d + 1) * a j := by ring
  have hlt : (i : ℕ) < j := hij
  have hd := key ((j : ℕ) - i) i j (by omega)
  calc a i ≤ 2 ^ ((j : ℕ) - i) * a j := hd
    _ ≤ 2 ^ N * a j :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by have := j.isLt; omega))
        (ha j).le
open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma exists_reduced_iwasawa_decomposition {ι : Type} [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] (g : Matrix ι ι ℝ) (hg : g.det ≠ 0) :
    ∃ (γ : Matrix ι ι ℤ) (k : Matrix ι ι ℝ) (a : ι → ℝ) (n : Matrix ι ι ℝ),
      (γ.det = 1 ∨ γ.det = -1) ∧ kᵀ * k = 1 ∧ (∀ i, 0 < a i) ∧ (∀ i, n i i = 1) ∧
      (∀ i j, j < i → n i j = 0) ∧ (∀ i j, |n i j| ≤ 1) ∧
      (∀ i j, i < j → a i ≤ 2 ^ Fintype.card ι * a j) ∧
      g * γ.map (Int.cast : ℤ → ℝ) = k * diagonal a * n := by
  set N := Fintype.card ι
  let e : Fin N ≃o ι := Fintype.orderIsoFinOfCardEq ι rfl
  let f : Fin N ≃ ι := e.toEquiv
  have hmono : ∀ i j : ι, f.symm i < f.symm j ↔ i < j := by
    intro i j
    have := (e.lt_iff_lt (x := f.symm i) (y := f.symm j))
    simpa [f] using this
  obtain ⟨γ, k, a, n, hγ, hk, ha, hn1, hn0, hnb, hcons, hdec⟩ :=
    _root_.GlobalTheory.ClassFin.HermiteReduction.exists_reduced N (g.submatrix f f)
      (by rw [det_submatrix_equiv_self f g]; exact hg)
  refine ⟨γ.submatrix f.symm f.symm, k.submatrix f.symm f.symm, a ∘ f.symm,
    n.submatrix f.symm f.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [det_submatrix_equiv_self]; exact hγ
  · rw [transpose_submatrix, submatrix_mul_equiv, hk, submatrix_one_equiv]
  · exact fun i => ha _
  · exact fun i => hn1 _
  · intro i j hij
    exact hn0 _ _ ((hmono j i).mpr hij)
  · intro i j
    show |n (f.symm i) (f.symm j)| ≤ 1
    rcases lt_trichotomy (f.symm i) (f.symm j) with h | h | h
    · exact (hnb _ _ h).trans (by norm_num)
    · rw [h, hn1]; simp
    · rw [hn0 _ _ h]; simp
  · intro i j hij
    exact le_two_pow_mul_of_consecutive_le a ha hcons _ _ ((hmono i j).mpr hij)
  · have hg' : g = (g.submatrix f f).submatrix f.symm f.symm := by ext i j; simp
    rw [hg', ← submatrix_map, submatrix_mul_equiv, hdec, ← submatrix_diagonal_equiv,
      submatrix_mul_equiv, submatrix_mul_equiv]
open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma isSiegel_of_reduced {ι : Type} [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] {C : ℝ} {g : Matrix ι ι ℝ} {γ : Matrix ι ι ℤ} {k : Matrix ι ι ℝ}
    {a : ι → ℝ} {n : Matrix ι ι ℝ} (hC : 1 ≤ C) (hg : g.det = 1) (hγ : γ.det = 1)
    (hk : kᵀ * k = 1) (ha : ∀ i, 0 < a i) (hn1 : ∀ i, n i i = 1)
    (hn0 : ∀ i j, j < i → n i j = 0) (hnb : ∀ i j, |n i j| ≤ 1)
    (hlt : ∀ i j, i < j → a i ≤ C * a j)
    (hdec : g * γ.map (Int.cast : ℤ → ℝ) = k * diagonal a * n) :
    _root_.GlobalTheory.ClassFin.IsSiegel C k a n := by
  have hn : n.det = 1 := by
    rw [det_of_upperTriangular (by intro i j h; exact hn0 i j h)]
    simp [hn1]
  have hγR : (γ.map (Int.cast : ℤ → ℝ)).det = 1 := by
    rw [show γ.map (Int.cast : ℤ → ℝ) = (Int.castRingHom ℝ).mapMatrix γ from rfl,
      ← RingHom.map_det, hγ]
    simp
  have hdet : k.det * ∏ i, a i = 1 := by
    have := congrArg det hdec
    rw [det_mul, det_mul, det_mul, hg, hn, det_diagonal, hγR] at this
    linarith
  have hk2 : k.det * k.det = 1 := by
    have := congrArg det hk
    rwa [det_mul, det_transpose, det_one] at this
  have hprod : 0 < ∏ i, a i := Finset.prod_pos fun i _ => ha i
  have hk1 : k.det = 1 := by
    rcases mul_self_eq_one_iff.mp hk2 with h | h
    · exact h
    · exfalso
      rw [h] at hdet
      linarith
  refine ⟨hk, hk1, ha, ?_, hlt, hn1, hn0, fun i j => (hnb i j).trans hC⟩
  rw [hk1, one_mul] at hdet
  exact hdet
open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma exists_det_one_of_det_neg_one {ι : Type} [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] {g : Matrix ι ι ℝ} {γ : Matrix ι ι ℤ} {k : Matrix ι ι ℝ} {a : ι → ℝ}
    {n : Matrix ι ι ℝ} (hγ : γ.det = -1) (hk : kᵀ * k = 1) (hn1 : ∀ i, n i i = 1)
    (hn0 : ∀ i j, j < i → n i j = 0) (hnb : ∀ i j, |n i j| ≤ 1)
    (hdec : g * γ.map (Int.cast : ℤ → ℝ) = k * diagonal a * n) :
    ∃ (γ' : Matrix ι ι ℤ) (k' n' : Matrix ι ι ℝ), γ'.det = 1 ∧ k'ᵀ * k' = 1 ∧
      (∀ i, n' i i = 1) ∧ (∀ i j, j < i → n' i j = 0) ∧ (∀ i j, |n' i j| ≤ 1) ∧
      g * γ'.map (Int.cast : ℤ → ℝ) = k' * diagonal a * n' := by
  obtain ⟨i₀⟩ : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [det_isEmpty] at hγ
    norm_num at hγ
  set d : ι → ℤ := fun i => if i = i₀ then -1 else 1 with hd_def
  have hd : ∀ i, (d i : ℝ) * d i = 1 := by
    intro i; simp only [hd_def]; split_ifs <;> norm_num
  have hda : ∀ i, |(d i : ℝ)| = 1 := by
    intro i; simp only [hd_def]; split_ifs <;> norm_num
  set D : Matrix ι ι ℝ := diagonal (fun i => (d i : ℝ)) with hD
  have hDD : D * D = 1 := by
    rw [hD, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact hd i
  have hcomm : D * diagonal a = diagonal a * D := by
    rw [hD, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  have hentry : ∀ i j, (D * n * D) i j = d i * n i j * d j := by
    intro i j
    simp [hD, mul_diagonal, diagonal_mul]
  refine ⟨γ * diagonal d, k * D, D * n * D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [det_mul, hγ, det_diagonal]
    have : ∏ i, d i = -1 := by
      simp [hd_def, Finset.prod_ite_eq']
    rw [this]; norm_num
  · rw [transpose_mul, hD, diagonal_transpose, ← hD, Matrix.mul_assoc, ← Matrix.mul_assoc kᵀ,
      hk, Matrix.one_mul, hDD]
  · intro i
    rw [hentry, hn1, mul_one]
    exact hd i
  · intro i j hij
    rw [hentry, hn0 i j hij]; simp
  · intro i j
    rw [hentry, abs_mul, abs_mul, hda, hda]
    simpa using hnb i j
  · have hmap : (γ * diagonal d).map (Int.cast : ℤ → ℝ) = γ.map (Int.cast) * D := by
      ext i j
      simp [hD, mul_diagonal]
    rw [hmap, ← Matrix.mul_assoc, hdec]
    calc k * diagonal a * n * D = k * (D * D) * diagonal a * n * D := by
          rw [hDD, Matrix.mul_one]
      _ = k * D * diagonal a * (D * n * D) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (diagonal a) D (n * D), ← hcomm]
          simp only [Matrix.mul_assoc]
end GlobalTheory.ClassFin
end

set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin
open Matrix
open scoped Kronecker ComplexOrder TensorProduct
namespace GlobalTheory.ClassFin
namespace _root_.GlobalTheory.ClassFin
theorem _root_.solution (ι : Type) [Fintype ι] [DecidableEq ι] [LinearOrder ι] :
    ∃ C : ℝ, ∀ g : Matrix ι ι ℝ, g.det = 1 → ∃ γ : Matrix ι ι ℤ, γ.det = 1 ∧ ∃ k a n, _root_.GlobalTheory.ClassFin.IsSiegel C k a n ∧
      g * γ.map (Int.cast : ℤ → ℝ) = k * diagonal a * n := by
  refine ⟨2 ^ Fintype.card ι, fun g hg => ?_⟩
  have hC : (1 : ℝ) ≤ 2 ^ Fintype.card ι := one_le_pow₀ (by norm_num)
  obtain ⟨γ, k, a, n, hγ, hk, ha, hn1, hn0, hnb, hlt, hdec⟩ :=
    exists_reduced_iwasawa_decomposition g (by rw [hg]; norm_num)
  rcases hγ with hγ | hγ
  · exact ⟨γ, hγ, k, a, n,
      isSiegel_of_reduced hC hg hγ hk ha hn1 hn0 hnb hlt hdec, hdec⟩
  · obtain ⟨γ', k', n', hγ', hk', hn1', hn0', hnb', hdec'⟩ :=
      exists_det_one_of_det_neg_one hγ hk hn1 hn0 hnb hdec
    exact ⟨γ', hγ', k', a, n',
      isSiegel_of_reduced hC hg hγ' hk' ha hn1' hn0' hnb' hlt hdec', hdec'⟩
end _root_.GlobalTheory.ClassFin
end GlobalTheory.ClassFin
