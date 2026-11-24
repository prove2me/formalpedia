-- Prove2me | solution 1 for GlobalTheory.LocBounded.bounded_of_isIntegral_general
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:10:13.76202+00:00
-- url     : https://prove2.me/submissions/5754cc90-6d95-4bdb-91f0-05264e12b270

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootsCharpolyPowEqMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BoundedOfIsIntegral
import Theorems.Thm_GlobalTheory_LocBounded_isIntegral_mul_of_commute
import Theorems.Thm_GlobalTheory_LocBounded_isIntegral_trace_of_isIntegral
import Theorems.Thm_GlobalTheory_LocBounded_exists_coeffs_of_mem_adjoin
import Theorems.Thm_GlobalTheory_LocBounded_det_hankel_trace_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
noncomputable section
open GlobalTheory GlobalTheory.LocBounded
namespace GlobalTheory.LocBounded
theorem _root_.solution {K Γ O : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [CommRing O] [Algebra O K]
    (hOv : ∀ y : O, v (algebraMap O K y) ≤ 1)
    (hvO : ∀ x : K, v x ≤ 1 → ∃ y : O, algebraMap O K y = x)
    (hint : ∀ x : K, IsIntegral O x → v x ≤ 1)
    {n : ℕ} (N : Matrix (Fin n) (Fin n) K) (hsep : N.charpoly.Separable) :
    ∃ c : Γ, ∀ g ∈ Algebra.adjoin K {N}, IsIntegral O g → ∀ i j, v (g i j) ≤ c := by
  classical
  obtain ⟨a, ha0, haN⟩ : ∃ a : K, a ≠ 0 ∧ ∀ i j, v (a * N i j) ≤ 1 := by
    by_cases h : ∀ i j, v (N i j) ≤ 1
    · exact ⟨1, one_ne_zero, fun i j => by simpa using h i j⟩
    · push_neg at h
      obtain ⟨i0, j0, h0⟩ := h
      obtain ⟨p, -, hp⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
        (fun p => v (N p.1 p.2)) ⟨(i0, j0), Finset.mem_univ _⟩
      have hpos : 1 < v (N p.1 p.2) := lt_of_lt_of_le h0 (hp (i0, j0) (Finset.mem_univ _))
      have hne : N p.1 p.2 ≠ 0 := fun h => by
        rw [h, map_zero] at hpos; exact absurd hpos (not_lt.2 zero_le')
      refine ⟨(N p.1 p.2)⁻¹, inv_ne_zero hne, fun i j => ?_⟩
      rw [map_mul, map_inv₀, inv_mul_le_iff₀ (zero_lt_one.trans hpos), mul_one]
      exact hp (i, j) (Finset.mem_univ _)
  let N0 : Matrix (Fin n) (Fin n) O := fun i j => (hvO _ (haN i j)).choose
  let φ : Matrix (Fin n) (Fin n) O →ₐ[O] Matrix (Fin n) (Fin n) K := (Algebra.ofId O K).mapMatrix
  have hφN : φ N0 = a • N := by
    ext i j
    exact (hvO _ (haN i j)).choose_spec
  let B : ℕ → Matrix (Fin n) (Fin n) K := fun k => (a • N) ^ k
  have hBφ : ∀ k, B k = φ (N0 ^ k) := fun k => by simp only [B, map_pow, hφN]
  have hBent : ∀ k i j, v (B k i j) ≤ 1 := by
    intro k i j
    rw [hBφ k]
    exact hOv _
  have hBint : ∀ k, IsIntegral O (B k) := fun k => by
    rw [hBφ k]; exact (Algebra.IsIntegral.isIntegral (N0 ^ k)).map φ
  have hBpow : ∀ k, B k = a ^ k • N ^ k := fun k => _root_.smul_pow a N k
  set T : Matrix (Fin n) (Fin n) K := Matrix.of fun j k : Fin n => (B j * B k).trace
  have hT : T.det ≠ 0 := by
    have hS := det_hankel_trace_ne_zero K n N hsep
    have e : T = Matrix.of fun j k : Fin n => a ^ (j : ℕ) * (Matrix.of fun j k : Fin n =>
        a ^ (k : ℕ) * (Matrix.of fun j k : Fin n => (N ^ ((j : ℕ) + (k : ℕ))).trace) j k) j k := by
      ext j k
      simp only [T, Matrix.of_apply, hBpow, smul_mul_smul_comm, ← pow_add, Matrix.trace_smul,
        smul_eq_mul]
      ring
    rw [e, Matrix.det_mul_column, Matrix.det_mul_row]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun _ _ => pow_ne_zero _ ha0)
      (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun _ _ => pow_ne_zero _ ha0) hS)
  refine ⟨Finset.univ.sup fun p : Fin n × Fin n => v (T⁻¹ p.1 p.2), ?_⟩
  intro g hg hgi
  obtain ⟨c0, hc0⟩ := exists_coeffs_of_mem_adjoin N hg
  set c : Fin n → K := fun k => c0 k / a ^ (k : ℕ)
  have hgc : g = ∑ k, c k • B k := by
    rw [hc0]; refine Finset.sum_congr rfl fun k _ => ?_
    rw [hBpow, smul_smul, div_mul_cancel₀ _ (pow_ne_zero _ ha0)]
  have hcomm : ∀ k, Commute g (B k) := by
    intro k
    rw [hc0, hBpow]
    refine Commute.sum_left _ _ _ fun l _ => ?_
    exact ((Commute.pow_pow_self N l k).smul_left _).smul_right _
  have ht : ∀ j, v ((g * B j).trace) ≤ 1 := fun j =>
    hint _ (isIntegral_trace_of_isIntegral (g * B j)
      (isIntegral_mul_of_commute (hcomm j) hgi (hBint j)))
  have hTc : T.mulVec c = fun j : Fin n => (g * B j).trace := by
    ext j
    simp only [Matrix.mulVec, dotProduct, T, Matrix.of_apply]
    rw [hgc, Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_mul_assoc, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm (B k) (B j), mul_comm]
  have hc : c = T⁻¹.mulVec fun j => (g * B j).trace := by
    rw [← hTc, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hT),
      Matrix.one_mulVec]
  have hcv : ∀ k, v (c k) ≤ Finset.univ.sup fun p : Fin n × Fin n => v (T⁻¹ p.1 p.2) := by
    intro k
    rw [hc]
    simp only [Matrix.mulVec, dotProduct]
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul, ← mul_one (Finset.univ.sup _)]
    exact mul_le_mul' (Finset.le_sup (f := fun p : Fin n × Fin n => v (T⁻¹ p.1 p.2))
      (Finset.mem_univ (k, l))) (ht l)
  intro i j
  rw [hgc, Matrix.sum_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, map_mul, ← mul_one (Finset.univ.sup _)]
  exact mul_le_mul' (hcv k) (hBent k i j)
end GlobalTheory.LocBounded
