-- Prove2me | solution 1 for GlobalTheory.commute_of_commute_separable_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:31:57.27258+00:00
-- url     : https://prove2.me/submissions/623b8542-d83a-4809-853e-88f5db00f702

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommuteOfCommuteSeparableCharpoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Polynomial
namespace GlobalTheory
open Matrix Polynomial in
private theorem exists_eigenvector_of_isRoot_charpoly {L : Type} [Field L] {n : ℕ}
    (y : Matrix (Fin n) (Fin n) L) (r : L) (h : y.charpoly.IsRoot r) :
    ∃ v : Fin n → L, v ≠ 0 ∧ y *ᵥ v = r • v := by
  rw [← Matrix.mem_spectrum_iff_isRoot_charpoly, spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero, not_not, ← Matrix.exists_mulVec_eq_zero_iff] at h
  obtain ⟨v, hv0, hv⟩ := h
  refine ⟨v, hv0, ?_⟩
  rw [Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec,
    sub_eq_zero] at hv
  exact hv.symm
open Matrix Polynomial in
private theorem isUnit_of_eigenvector_columns_of_injective {L : Type} [Field L] {n : ℕ}
    (y : Matrix (Fin n) (Fin n) L) (μ : Fin n → L) (hμ : Function.Injective μ)
    (v : Fin n → Fin n → L) (hv0 : ∀ j, v j ≠ 0) (hv : ∀ j, y *ᵥ v j = μ j • v j) :
    IsUnit (Matrix.of fun i j => v j i) := by
  rw [← Matrix.linearIndependent_cols_iff_isUnit]
  exact Module.End.eigenvectors_linearIndependent' (Matrix.toLin' y) μ hμ v
    (fun j => ⟨Module.End.mem_eigenspace_iff.mpr (by simpa using hv j), hv0 j⟩)
open Matrix Polynomial in
private theorem eq_diagonal_of_commute_diagonal_injective {L : Type} [Field L] {n : ℕ}
    (μ : Fin n → L) (hμ : Function.Injective μ) (m : Matrix (Fin n) (Fin n) L)
    (hm : m * diagonal μ = diagonal μ * m) : m = diagonal fun i => m i i := by
  ext i j
  have hij := congrFun (congrFun hm i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hij
  by_cases h : i = j
  · subst h
    simp
  · rw [Matrix.diagonal_apply_ne _ h]
    have hne : μ j - μ i ≠ 0 := sub_ne_zero.mpr fun e => h (hμ e).symm
    have : m i j * (μ j - μ i) = 0 := by rw [mul_sub, hij, mul_comm]; ring
    exact (mul_eq_zero.mp this).resolve_right hne
open Matrix Polynomial in
private theorem commute_of_commute_of_charpoly_separable_of_isAlgClosed {L : Type} [Field L]
    [IsAlgClosed L] {n : ℕ} (y a b : Matrix (Fin n) (Fin n) L) (hy : y.charpoly.Separable)
    (ha : a * y = y * a) (hb : b * y = y * b) : a * b = b * a := by
  classical
  set s := y.charpoly.roots.toFinset with hs_def
  have hs : s.card = n := by
    rw [hs_def, Multiset.toFinset_card_of_nodup (nodup_roots hy),
      IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  let e : Fin n ≃ s := (s.equivFin.trans (finCongr hs)).symm
  let μ : Fin n → L := fun i => (e i : L)
  have hμ : Function.Injective μ := fun i j hij => e.injective (Subtype.ext hij)
  have hroot : ∀ i, y.charpoly.IsRoot (μ i) := fun i => by
    have hmem : (μ i) ∈ s := (e i).2
    rw [hs_def, Multiset.mem_toFinset] at hmem
    exact (mem_roots hy.ne_zero).mp hmem
  choose v hv0 hv using fun i => exists_eigenvector_of_isRoot_charpoly y (μ i) (hroot i)
  set P : Matrix (Fin n) (Fin n) L := Matrix.of fun i j => v j i with hP
  have hPu : IsUnit P := isUnit_of_eigenvector_columns_of_injective y μ hμ v hv0 hv
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  set Q := P⁻¹ with hQ
  have hPQ : P * Q = 1 := Matrix.mul_nonsing_inv P hdet
  have hQP : Q * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hPQ' : ∀ X : Matrix (Fin n) (Fin n) L, P * (Q * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hQP' : ∀ X : Matrix (Fin n) (Fin n) L, Q * (P * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hyP : y * P = P * diagonal μ := by
    ext i j
    rw [Matrix.mul_diagonal]
    have := congrFun (hv j) i
    simpa [hP, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using this
  have hD : Q * y * P = diagonal μ := by
    rw [Matrix.mul_assoc, hyP, hQP']
  have hcomm : ∀ m : Matrix (Fin n) (Fin n) L, m * y = y * m →
      (Q * m * P) * diagonal μ = diagonal μ * (Q * m * P) := fun m hm => by
    rw [← hD]
    simp only [Matrix.mul_assoc, hPQ']
    rw [← Matrix.mul_assoc m y P, hm, Matrix.mul_assoc]
  have hA := eq_diagonal_of_commute_diagonal_injective μ hμ _ (hcomm a ha)
  have hB := eq_diagonal_of_commute_diagonal_injective μ hμ _ (hcomm b hb)
  have hAB : (Q * a * P) * (Q * b * P) = (Q * b * P) * (Q * a * P) := by
    rw [hA, hB, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have key : ∀ c d : Matrix (Fin n) (Fin n) L, c * d = P * ((Q * c * P) * (Q * d * P)) * Q :=
    fun c d => by
      simp only [Matrix.mul_assoc, hPQ', hPQ, Matrix.mul_one]
  rw [key a b, key b a, hAB]
end GlobalTheory
end

set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory
open Matrix Polynomial
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] (n : ℕ) (y a b : Matrix (Fin n) (Fin n) K), y.charpoly.Separable →
      a * y = y * a → b * y = y * b → a * b = b * a := by
  intro K _ n y a b hy ha hb
  let f : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have hyL : (y.map f).charpoly.Separable := by
    rw [Matrix.charpoly_map]
    exact hy.map
  have haL : a.map f * y.map f = y.map f * a.map f := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ha]
  have hbL : b.map f * y.map f = y.map f * b.map f := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hb]
  have h := commute_of_commute_of_charpoly_separable_of_isAlgClosed _ _ _ hyL haL hbL
  rw [← Matrix.map_mul, ← Matrix.map_mul] at h
  exact Matrix.map_injective f.injective h
end _root_.GlobalTheory
end GlobalTheory
