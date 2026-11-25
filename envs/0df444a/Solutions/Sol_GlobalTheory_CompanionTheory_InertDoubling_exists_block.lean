-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertDoubling.exists_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:40:25.02083+00:00
-- url     : https://prove2.me/submissions/59aa0b00-b403-463d-a033-31945fb39480

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CompletionExists
import Theorems.Thm_GlobalTheory_CompanionTheory_InertDoubling_ring_gram
import Theorems.Thm_GlobalTheory_CompanionTheory_InertDoubling_ring_pair
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_InertDoubling_cT_add__39925ac7f366
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_InertDoubling_cT_sub__36510c354772
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_InertDoubling_cT_neg__13e72bb0d4ba
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_InertDoubling_cT_smul__d0f49d90ce33
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_InertDoubling_cT_cT__9662d98d970f
import Theorems.Thm_GlobalTheory_CompanionTheory_InertDoubling_cT_fromBlocks
import Theorems.Thm_GlobalTheory_CompanionTheory_InertDoubling_isInt_fromBlocks
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_InertDoubling_isInt_neg__419bce61802a
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_InertDoubling_isInt_sub__879aecc3fdb2
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_InertDoubling_isInt_smul__901e0850cacc
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_InertDoubling_isInt_cT__4f5a9b0f6f2c
import Theorems.Thm_GlobalTheory_CompanionTheory_InertDoubling_isInt_antiJ
import Theorems.Thm_GlobalTheory_CompanionTheory_InertDoubling_cT_antiJ
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_IsInt_add
import Theorems.Thm_GlobalTheory_InertZeta_IsInt_mul
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_isInt_one
import Theorems.Thm_GlobalTheory_InertZeta_isInt_zero
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
import Theorems.Thm_GlobalTheory_UnitarySwap_SelfDual_add
import Theorems.Thm_GlobalTheory_UnitarySwap_antiJ_mul_self
import Theorems.Thm_GlobalTheory_UnitarySwap_mem_int
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.InertZeta.blk_last
attribute [local simp] GlobalTheory.InertZeta.blk_mid
attribute [local simp] GlobalTheory.InertZeta.blk_zero
attribute [local simp] GlobalTheory.InertZeta.val_mid



set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.Doubling GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertDoubling
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
namespace GlobalTheory.CompanionTheory.InertDoubling
theorem _root_.solution (hσσ : ∀ x, σ (σ x) = x) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {τ : L} (hτ : τ ∈ intL L)
    (hτ1 : τ + σ τ = 1) {A B U V : Matrix (Fin n) (Fin n) L} (hA : IsInt A) (hB : IsInt B) (hU : IsInt U) (hV : IsInt V)
    (hAB : cT σ A * antiJ L n * A = cT σ B * antiJ L n * B) (hUV : U * A + V * B = 1) :
    ∃ k₀ k₁ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, IsInt k₀ ∧ IsInt k₁ ∧ k₁ * k₀ = 1 ∧
      cT σ k₀ * fromBlocks (antiJ L n) 0 0 (-antiJ L n) * k₀ = fromBlocks (antiJ L n) 0 0 (-antiJ L n) ∧
      k₀.toBlocks₁₁ + k₀.toBlocks₁₂ = A ∧ k₀.toBlocks₂₁ + k₀.toBlocks₂₂ = B := by
  obtain ⟨J, hJdef⟩ : ∃ J, J = antiJ L n := ⟨_, rfl⟩
  rw [← hJdef] at hAB ⊢
  have hJ : J * J = 1 := hJdef ▸ GlobalTheory.UnitarySwap.antiJ_mul_self
  have hJc : cT σ J = J := hJdef ▸ cT_antiJ σ n
  have hJi : IsInt J := hJdef ▸ isInt_antiJ n
  have hτ' : σ τ ∈ intL L := by rw [GlobalTheory.UnitarySwap.mem_int, hσv]; exact hτ
  obtain ⟨R, hR⟩ : ∃ R, R = U * J * cT σ U - V * J * cT σ V := ⟨_, rfl⟩
  have hRc : cT σ R = R := by
    rw [hR]; simp only [cT_sub', cT_mul, cT_cT' hσσ, hJc, Matrix.mul_assoc]
  have hRi : IsInt R := hR ▸ isInt_sub' ((hU.mul hJi).mul (isInt_cT' hσv hU)) ((hV.mul hJi).mul (isInt_cT' hσv hV))
  obtain ⟨S, hS⟩ : ∃ S, S = -(τ • (R * J)) := ⟨_, rfl⟩
  have hSc : cT σ S = -(σ τ • (J * R)) := by rw [hS, cT_neg', cT_smul', cT_mul, hRc, hJc]
  have hSi : IsInt S := hS ▸ isInt_neg' (isInt_smul' hτ (hRi.mul hJi))
  obtain ⟨Ψ₁, hΨ₁⟩ : ∃ Ψ, Ψ = J * cT σ U * J + A * S := ⟨_, rfl⟩
  obtain ⟨Ψ₂, hΨ₂⟩ : ∃ Ψ, Ψ = -(J * cT σ V * J) + B * S := ⟨_, rfl⟩
  have hΨ₁i : IsInt Ψ₁ := hΨ₁ ▸ ((hJi.mul (isInt_cT' hσv hU)).mul hJi).add (hA.mul hSi)
  have hΨ₂i : IsInt Ψ₂ := hΨ₂ ▸ (isInt_neg' ((hJi.mul (isInt_cT' hσv hV)).mul hJi)).add (hB.mul hSi)
  have h2 : cT σ A * cT σ U + cT σ B * cT σ V = 1 := by
    have := congrArg (cT σ) hUV
    rwa [cT_add', cT_mul, cT_mul, cT_one] at this
  have g12 : cT σ A * J * Ψ₁ - cT σ B * J * Ψ₂ = J := by
    rw [hΨ₁, hΨ₂]; exact ring_pair J A B U V _ _ _ _ S hJ h2 hAB
  have g21 : cT σ Ψ₁ * J * A - cT σ Ψ₂ * J * B = J := by
    have := congrArg (cT σ) g12
    simpa only [cT_sub', cT_mul, cT_cT' hσσ, hJc, Matrix.mul_assoc] using this
  have cΨ₁ : cT σ Ψ₁ = J * U * J + cT σ S * cT σ A := by
    rw [hΨ₁]; simp only [cT_add', cT_mul, cT_cT' hσσ, hJc, Matrix.mul_assoc]
  have cΨ₂ : cT σ Ψ₂ = -(J * V * J) + cT σ S * cT σ B := by
    rw [hΨ₂]; simp only [cT_add', cT_neg', cT_mul, cT_cT' hσσ, hJc, Matrix.mul_assoc]
  have g22 : cT σ Ψ₁ * J * Ψ₁ - cT σ Ψ₂ * J * Ψ₂ = 0 := by
    rw [cΨ₁, cΨ₂, hΨ₁, hΨ₂, ring_gram J A B U V _ _ _ _ S _ hJ hUV h2 hAB, ← hR, hSc, hS]
    have e : J * R * J + J * -(τ • (R * J)) + -(σ τ • (J * R)) * J = (1 - τ - σ τ) • (J * R * J) := by
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, sub_smul, one_smul]
      abel
    rw [e, show 1 - τ - σ τ = 0 by linear_combination -hτ1, zero_smul]
  have e1 : σ τ • (1 : Matrix (Fin n) (Fin n) L) + τ • 1 = 1 := by rw [← add_smul, add_comm, hτ1, one_smul]
  have e2 : σ τ • J + τ • J = J := by rw [← add_smul, add_comm, hτ1, one_smul]
  obtain ⟨Jd, hJd⟩ : ∃ Jd : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, Jd = fromBlocks J 0 0 (-J) := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, H = fromBlocks 0 J J 0 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, D = fromBlocks 1 (τ • 1) 1 (-(σ τ • 1)) := ⟨_, rfl⟩
  obtain ⟨Di, hDi⟩ : ∃ D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, D = fromBlocks (σ τ • 1) (τ • 1) 1 (-1) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, P = fromBlocks A Ψ₁ B Ψ₂ := ⟨_, rfl⟩
  have hDDi : D * Di = 1 := by
    rw [hD, hDi, fromBlocks_multiply, ← fromBlocks_one]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_neg, Matrix.neg_mul, neg_neg, smul_neg]
    rw [fromBlocks_inj]
    refine ⟨e1, by simp, by simp, ?_⟩
    rw [add_comm]; exact e1
  have hHH : H * H = 1 := by
    rw [hH, fromBlocks_multiply, ← fromBlocks_one]
    simp [hJ]
  have hDg : cT σ D * Jd * D = H := by
    rw [hD, hJd, hH, cT_fromBlocks, fromBlocks_multiply, fromBlocks_multiply]
    simp only [cT_neg', cT_smul', cT_one, hσσ, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_neg, neg_neg, smul_neg]
    rw [fromBlocks_inj]
    refine ⟨by simp, by rw [add_comm]; exact e2, e2, ?_⟩
    rw [smul_comm, add_neg_cancel]
  have hPg : cT σ P * Jd * P = H := by
    rw [hP, hJd, hH, cT_fromBlocks, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg]
    simp only [← sub_eq_add_neg]
    rw [fromBlocks_inj]
    exact ⟨sub_eq_zero.2 hAB, g12, g21, g22⟩
  have hDi' : IsInt Di := hDi ▸ isInt_fromBlocks (isInt_smul' hτ' isInt_one) (isInt_smul' hτ isInt_one) isInt_one (isInt_neg' isInt_one)
  have hDint : IsInt D := hD ▸ isInt_fromBlocks isInt_one (isInt_smul' hτ isInt_one) isInt_one (isInt_neg' (isInt_smul' hτ' isInt_one))
  have hPi : IsInt P := hP ▸ isInt_fromBlocks hA hΨ₁i hB hΨ₂i
  have hHi : IsInt H := hH ▸ isInt_fromBlocks isInt_zero hJi hJi isInt_zero
  have hJdi : IsInt Jd := hJd ▸ isInt_fromBlocks hJi isInt_zero isInt_zero (isInt_neg' hJi)
  refine ⟨P * Di, D * H * cT σ P * Jd, hPi.mul hDi', ((hDint.mul hHi).mul (isInt_cT' hσv hPi)).mul hJdi, ?_, ?_, ?_, ?_⟩
  · calc D * H * cT σ P * Jd * (P * Di) = D * H * (cT σ P * Jd * P) * Di := by simp only [Matrix.mul_assoc]
      _ = D * (H * H) * Di := by rw [hPg]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hHH, Matrix.mul_one, hDDi]
  · rw [← hJd]
    calc cT σ (P * Di) * Jd * (P * Di) = cT σ Di * (cT σ P * Jd * P) * Di := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT σ Di * (cT σ D * Jd * D) * Di := by rw [hPg, hDg]
      _ = cT σ (D * Di) * Jd * (D * Di) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = Jd := by rw [hDDi, cT_one, Matrix.one_mul, Matrix.mul_one]
  · rw [hP, hDi, fromBlocks_multiply, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂]
    simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.mul_neg]
    rw [show σ τ • A + Ψ₁ + (τ • A + -Ψ₁) = (τ + σ τ) • A by rw [add_smul]; abel, hτ1, one_smul]
  · rw [hP, hDi, fromBlocks_multiply, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
    simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.mul_neg]
    rw [show σ τ • B + Ψ₂ + (τ • B + -Ψ₂) = (τ + σ τ) • B by rw [add_smul]; abel, hτ1, one_smul]
end GlobalTheory.CompanionTheory.InertDoubling
