-- Prove2me | solution 1 for GlobalTheory.exists_basis_adapted_to_cartan_involution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:36:10.900353+00:00
-- url     : https://prove2.me/submissions/67963223-68be-405c-ae72-886b2e484047

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasisAdaptedToCartanInvolution
import Theorems.Thm_GlobalTheory_posDef_exists_invertible_conjTranspose_mul_self
import Theorems.Thm_GlobalTheory_hermitian_involution_unitary_blocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (n : ℕ) (G s : Matrix (Fin n) (Fin n) ℂ), s * s = 1 → sᴴ * G * s = G → (G * s).PosDef →
      ∃ (p q : ℕ) (B : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ)
        (B' : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ), B * B' = 1 ∧ B' * B = 1 ∧
        Bᴴ * G * B = Matrix.fromBlocks 1 0 0 (-1) ∧
        s * B = B * Matrix.fromBlocks 1 0 0 (-1) := by
  intro n G s hs hG hP
  obtain ⟨R, Ri, h1, h2, hR⟩ := posDef_exists_invertible_conjTranspose_mul_self _ hP
  have hG1 : G = Rᴴ * R * s := by rw [← hR, Matrix.mul_assoc, hs, Matrix.mul_one]
  have hG2 : G = sᴴ * (Rᴴ * R) := by rw [← hR, ← Matrix.mul_assoc, hG]
  have h3 : Riᴴ * Rᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have hGt : Riᴴ * G * Ri = R * s * Ri := by
    rw [hG1]
    calc Riᴴ * (Rᴴ * R * s) * Ri = (Riᴴ * Rᴴ) * (R * s * Ri) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h3, Matrix.one_mul]
  have hherm : (R * s * Ri)ᴴ = R * s * Ri := by
    rw [← hGt]
    conv_rhs => rw [hG2]
    rw [hGt]
    calc (R * s * Ri)ᴴ = Riᴴ * sᴴ * Rᴴ * (R * Ri) := by
          rw [h1]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hinv : (R * s * Ri) * (R * s * Ri) = 1 := by
    calc (R * s * Ri) * (R * s * Ri) = R * (s * (Ri * R) * s) * Ri := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h2, Matrix.mul_one, hs, Matrix.mul_one, h1]
  obtain ⟨p, q, V, hV1, hV2, hV3⟩ := hermitian_involution_unitary_blocks _ hherm hinv
  refine ⟨p, q, Ri * V, Vᴴ * R, ?_, ?_, ?_, ?_⟩
  · calc Ri * V * (Vᴴ * R) = Ri * (V * Vᴴ) * R := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hV1, Matrix.mul_one, h2]
  · calc Vᴴ * R * (Ri * V) = Vᴴ * (R * Ri) * V := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, hV2]
  · rw [← hV3, ← hGt]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  · rw [← hV3]
    symm
    calc Ri * V * (Vᴴ * (R * s * Ri) * V) = Ri * (V * Vᴴ) * R * (s * (Ri * V)) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV1, Matrix.mul_one, h2, Matrix.one_mul]
end GlobalTheory
