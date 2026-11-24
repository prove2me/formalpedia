-- Prove2me | solution 1 for GlobalTheory.antidiag_twisted_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:22:19.676642+00:00
-- url     : https://prove2.me/submissions/5482e9d6-a946-4077-9b37-b125eb2856d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AntidiagTwistedNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] (c : E ≃+* E), (∀ x, c (c x) = x) → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) E), Φ = Matrix.of (fun i j : Fin a => if j = i.rev then (-1 : E) ^ (i : ℕ) else 0) → Φ.transpose = (-1 : E) ^ (a - 1) • Φ ∧ IsUnit Φ.det ∧ ∀ δ : Matrix (Fin a) (Fin a) E, IsUnit δ.det → δ * (Φ * ((δ.map c).transpose)⁻¹ * Φ⁻¹) = (-1 : E) ^ (a - 1) • ((δ * Φ) * (((δ * Φ).map c).transpose)⁻¹) ∧ Φ * (((Φ * ((δ.map c).transpose)⁻¹ * Φ⁻¹).map c).transpose)⁻¹ * Φ⁻¹ = δ := by
  intro E _ c hc a Φ hΦ
  have hpm : ∀ n : ℕ, (-1 : E) ^ n * (-1 : E) ^ n = 1 := by
    intro n; rw [← mul_pow]; simp
  have hss : (-1 : E) ^ (a - 1) * (-1 : E) ^ (a - 1) = 1 := hpm _
  have hsign : ∀ i : Fin a, (-1 : E) ^ (i.rev : ℕ) = (-1 : E) ^ (a - 1) * (-1 : E) ^ (i : ℕ) := by
    intro i
    have hi := i.isLt
    rw [Fin.val_rev, ← pow_add]
    have : a - 1 + (i:ℕ) = (a - ((i:ℕ) + 1)) + 2 * (i:ℕ) := by omega
    rw [this, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
  have hT : Φ.transpose = (-1 : E) ^ (a - 1) • Φ := by
    subst hΦ
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases h : j = i.rev
    · subst h
      simp only [Fin.rev_rev, if_true]
      exact hsign i
    · have h' : ¬ i = j.rev := by
        intro h2; apply h; rw [h2, Fin.rev_rev]
      simp [h, h']
  have hsq : Φ * Φ = (-1 : E) ^ (a - 1) • (1 : Matrix (Fin a) (Fin a) E) := by
    subst hΦ
    ext i k
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i.rev]
    · by_cases h : k = i
      · subst h
        simp only [Fin.rev_rev, if_true, hsign]
        rw [mul_one, mul_left_comm, hpm, mul_one]
      · have : ¬ k = i.rev.rev := by rwa [Fin.rev_rev]
        simp [this, h, Ne.symm h]
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hright : Φ * Φ.transpose = 1 := by
    rw [hT, Matrix.mul_smul, hsq, smul_smul, hss, one_smul]
  have hleft : Φ.transpose * Φ = 1 := by
    rw [hT, Matrix.smul_mul, hsq, smul_smul, hss, one_smul]
  have hinv : Φ⁻¹ = Φ.transpose := Matrix.inv_eq_left_inv hleft
  have hTinv : (Φ.transpose)⁻¹ = Φ := Matrix.inv_eq_left_inv hright
  have hdet : IsUnit Φ.det := Matrix.isUnit_det_of_left_inverse hleft
  have hΦc : Φ.map c = Φ := by
    subst hΦ
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  have hmapmul : ∀ A B : Matrix (Fin a) (Fin a) E, (A * B).map c = A.map c * B.map c :=
    fun A B => Matrix.map_mul (f := (c : E →+* E))
  have hmapinv : ∀ A : Matrix (Fin a) (Fin a) E, IsUnit A.det → (A⁻¹).map c = (A.map c)⁻¹ := by
    intro A hA
    refine (Matrix.inv_eq_left_inv ?_).symm
    rw [← hmapmul, Matrix.nonsing_inv_mul _ hA, Matrix.map_one _ c.map_zero c.map_one]
  have hcc : ∀ A : Matrix (Fin a) (Fin a) E, (A.map c).map c = A := by
    intro A; ext i j; simp [hc]
  refine ⟨hT, hdet, fun δ hδ => ⟨?_, ?_⟩⟩
  · rw [hmapmul, hΦc, Matrix.transpose_mul, Matrix.mul_inv_rev, hTinv, hinv, hT]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  · have hYd : IsUnit ((δ.map c).transpose).det := by
      rw [Matrix.det_transpose]
      have h1 := RingHom.map_det (c : E →+* E) δ
      rw [RingHom.mapMatrix_apply] at h1
      have h2 : (δ.map c).det = c δ.det := h1.symm
      rw [h2]; exact hδ.map c
    have hΦTc : (Φ.transpose).map c = Φ.transpose := by rw [Matrix.transpose_map, hΦc]
    rw [hinv, hmapmul, hmapmul, hΦc, hΦTc, hmapinv _ hYd,
      Matrix.transpose_map, hcc, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_nonsing_inv, Matrix.transpose_transpose,
      Matrix.mul_inv_rev, Matrix.mul_inv_rev, hTinv, Matrix.nonsing_inv_nonsing_inv _ hδ, hinv]
    have e : Φ * (Φ * δ * Φ.transpose) * Φ.transpose = (Φ * Φ) * δ * (Φ.transpose * Φ.transpose) := by
      simp only [Matrix.mul_assoc]
    rw [e, ← Matrix.transpose_mul, hsq, Matrix.transpose_smul, Matrix.transpose_one,
      Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hss, one_smul]
end GlobalTheory
