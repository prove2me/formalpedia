-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CommonTransversal.exists_skew_isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:24:33.628863+00:00
-- url     : https://prove2.me/submissions/57049be4-adc6-412b-bdb6-e4cb14b02008

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsSkewOfDiagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CommonTransversal
namespace GlobalTheory.CompanionTheory.CommonTransversal
theorem _root_.solution {F : Type} [Field F] (σ : F →+* F) {β : Type} [Fintype β]
    [DecidableEq β] (a b : Matrix β β F) (hσ : ∀ z, σ (σ z) = z) (hz : ∃ z, σ z ≠ z)
    (h : a * (b.map σ)ᵀ + b * (a.map σ)ᵀ = 0)
    (hv : ∀ v : β → F, Matrix.vecMul v a = 0 → Matrix.vecMul v b = 0 → v = 0) :
    ∃ s : Matrix β β F, (s.map σ)ᵀ = -s ∧ IsUnit (a + b * s).det := by
  classical
  obtain ⟨L, L', D, hD⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec a
  obtain ⟨P, hP⟩ : ∃ P, P = (L.map Matrix.TransvectionStruct.toMatrix).prod := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (L'.map Matrix.TransvectionStruct.toMatrix).prod := ⟨_, rfl⟩
  rw [← hP, ← hQ] at hD
  have hP1 : P.det = 1 := by rw [hP]; exact Matrix.TransvectionStruct.det_toMatrix_prod L
  have hQ1 : Q.det = 1 := by rw [hQ]; exact Matrix.TransvectionStruct.det_toMatrix_prod L'
  have hst1 : ∀ M : Matrix β β F, M.det = 1 → ((M.map σ)ᵀ).det = 1 := by
    intro M hM
    rw [Matrix.det_transpose]
    have e : (M.map σ).det = σ M.det := (RingHom.map_det σ M).symm
    rw [e, hM, map_one]
  have cancel : ∀ (M : Matrix β β F) (x : β → F), M.det = 1 → x ᵥ* M = 0 → x = 0 := by
    intro M x hM hx
    have hu : IsUnit M.det := by rw [hM]; exact isUnit_one
    calc x = x ᵥ* (M * M⁻¹) := by rw [Matrix.mul_nonsing_inv (A := M) hu, Matrix.vecMul_one]
      _ = 0 := by rw [← Matrix.vecMul_vecMul, hx, Matrix.zero_vecMul]
  obtain ⟨z, hz⟩ := hz
  obtain ⟨c, hcdef⟩ : ∃ c, c = z - σ z := ⟨_, rfl⟩
  have hc : c ≠ 0 := by rw [hcdef]; exact sub_ne_zero.2 (Ne.symm hz)
  have hσc : σ c = -c := by rw [hcdef, map_sub, hσ]; ring
  obtain ⟨s0, hs0⟩ : ∃ s0 : Matrix β β F, s0 = diagonal (fun i => if D i = 0 then c else 0) :=
    ⟨_, rfl⟩
  have hss : (s0.map σ)ᵀ = -s0 := by
    rw [hs0, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.diagonal_neg]
    congr 1
    funext i
    split_ifs <;> simp [hσc]
  have hQQ : ((((Q.map σ)ᵀ).map σ)ᵀ) = Q := by
    ext i j
    simp [hσ]
  have hsta : (a.map σ)ᵀ = (Q.map σ)ᵀ * diagonal (fun i => σ (D i)) * (P.map σ)ᵀ := by
    rw [hD, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.mul_assoc]
  refine ⟨(Q.map σ)ᵀ * s0 * Q, ?_, ?_⟩
  · rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, hss, hQQ,
      Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc]
  · rw [isUnit_iff_ne_zero]
    intro hdet
    obtain ⟨v, hv0, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
    apply hv0
    have e1 : a + b * ((Q.map σ)ᵀ * s0 * Q) = (P * diagonal D + b * (Q.map σ)ᵀ * s0) * Q := by
      rw [hD]
      simp only [Matrix.add_mul, Matrix.mul_assoc]
    have h0 : v ᵥ* (P * diagonal D + b * (Q.map σ)ᵀ * s0) = 0 :=
      cancel Q _ hQ1 (by rw [Matrix.vecMul_vecMul, ← e1]; exact hvM)
    have h0' : (v ᵥ* P) ᵥ* diagonal D + ((v ᵥ* b) ᵥ* (Q.map σ)ᵀ) ᵥ* s0 = 0 := by
      simpa only [Matrix.vecMul_vecMul, Matrix.vecMul_add] using h0
    have hE : ∀ j, (v ᵥ* P) j * D j +
        ((v ᵥ* b) ᵥ* (Q.map σ)ᵀ) j * (if D j = 0 then c else 0) = 0 := by
      intro j
      have e := congr_fun h0' j
      rw [Pi.add_apply, Matrix.vecMul_diagonal, hs0, Matrix.vecMul_diagonal] at e
      exact e
    have hwD : (v ᵥ* P) ᵥ* diagonal D = 0 := by
      funext j
      rw [Matrix.vecMul_diagonal, Pi.zero_apply]
      by_cases hDj : D j = 0
      · rw [hDj, mul_zero]
      · have e := hE j
        rw [if_neg hDj, mul_zero, add_zero] at e
        rw [(mul_eq_zero.1 e).resolve_right hDj, zero_mul]
    have hva : v ᵥ* a = 0 := by
      rw [hD, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hwD, Matrix.zero_vecMul]
    have hc1 : v ᵥ* (a * (b.map σ)ᵀ + b * (a.map σ)ᵀ) = 0 := by rw [h, Matrix.vecMul_zero]
    rw [Matrix.vecMul_add, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hva, Matrix.zero_vecMul,
      zero_add, hsta, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul] at hc1
    have hud : ((v ᵥ* b) ᵥ* (Q.map σ)ᵀ) ᵥ* diagonal (fun i => σ (D i)) = 0 :=
      cancel _ _ (hst1 P hP1) hc1
    have hu : (v ᵥ* b) ᵥ* (Q.map σ)ᵀ = 0 := by
      funext j
      rw [Pi.zero_apply]
      by_cases hDj : D j = 0
      · have e := hE j
        rw [if_pos hDj, hDj, mul_zero, zero_add] at e
        exact (mul_eq_zero.1 e).resolve_right hc
      · have e := congr_fun hud j
        rw [Matrix.vecMul_diagonal, Pi.zero_apply] at e
        exact (mul_eq_zero.1 e).resolve_right ((map_ne_zero σ).2 hDj)
    exact hv v hva (cancel _ _ (hst1 Q hQ1) hu)
end GlobalTheory.CompanionTheory.CommonTransversal
