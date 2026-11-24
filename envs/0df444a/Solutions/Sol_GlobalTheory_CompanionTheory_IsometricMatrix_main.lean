-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IsometricMatrix.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:40:30.86332+00:00
-- url     : https://prove2.me/submissions/f1b6f0e9-f8ed-4ef6-89d6-451eabea3fc9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixExpSmulMulEqMulExpSmulOfIntertwine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockBasisChangeEntries
import Theorems.Thm_GlobalTheory_CompanionTheory_IsometricMatrix_exp_mulVec_of_mulVec_eq_zero
import Theorems.Thm_GlobalTheory_matrix_exp_smul_mul_eq_mul_exp_smul_of_intertwine


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IsometricMatrix
namespace GlobalTheory.CompanionTheory.IsometricMatrix
theorem _root_.solution {n n' : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (H' : Matrix (Fin n') (Fin n') ℂ)
    (J : Matrix (Fin n) (Fin n') ℂ)
    (hH : Hᴴ = H) (hH' : H'ᴴ = H') (hd : IsUnit H.det) (hd' : IsUnit H'.det)
    (hJ : Jᴴ * H * J = H') :
    ((H'⁻¹ * Jᴴ * H) * J = 1 ∧
      (∀ Z : Matrix (Fin n') (Fin n') ℂ, -(H⁻¹ * (J * Z * (H'⁻¹ * Jᴴ * H))ᴴ * H) = J * (-(H'⁻¹ * Zᴴ * H')) * (H'⁻¹ * Jᴴ * H)) ∧
      (∀ A : Matrix (Fin n') (Fin n') ℂ, Aᴴ * H' + H' * A = 0 →
        (J * A * (H'⁻¹ * Jᴴ * H))ᴴ * H + H * (J * A * (H'⁻¹ * Jᴴ * H)) = 0) ∧
      (∀ (A : Matrix (Fin n') (Fin n') ℂ) (t : ℝ), NormedSpace.exp (t • (J * A * (H'⁻¹ * Jᴴ * H))) * J = J * NormedSpace.exp (t • A)) ∧
      (∀ (A : Matrix (Fin n') (Fin n') ℂ) (t : ℝ) (x : Fin n → ℂ), (Jᴴ * H) *ᵥ x = 0 →
        NormedSpace.exp (t • (J * A * (H'⁻¹ * Jᴴ * H))) *ᵥ x = x)) := by
  have hJ' : Jᴴ * (H * J) = H' := by rw [← Matrix.mul_assoc]; exact hJ
  have hPJ : H'⁻¹ * Jᴴ * H * J = 1 := by
    simp only [Matrix.mul_assoc]
    rw [hJ', Matrix.nonsing_inv_mul _ hd']
  have hPs : (H'⁻¹ * Jᴴ * H)ᴴ = H * J * H'⁻¹ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_nonsing_inv, hH, hH', Matrix.mul_assoc]
  refine ⟨hPJ, fun Z => ?_, fun A hA => ?_, fun A t => ?_, fun A t x hx => ?_⟩
  · rw [Matrix.conjTranspose_mul (J * Z) (H'⁻¹ * Jᴴ * H), hPs, Matrix.conjTranspose_mul J Z]
    simp only [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.nonsing_inv_mul_cancel_left _ _ hd, Matrix.mul_nonsing_inv_cancel_left _ _ hd']
  · have key : H * J * H'⁻¹ * (Aᴴ * H' + H' * A) * (H'⁻¹ * Jᴴ * H) =
        (J * A * (H'⁻¹ * Jᴴ * H))ᴴ * H + H * (J * A * (H'⁻¹ * Jᴴ * H)) := by
      rw [Matrix.conjTranspose_mul (J * A) (H'⁻¹ * Jᴴ * H), hPs, Matrix.conjTranspose_mul J A,
        Matrix.mul_add, Matrix.add_mul]
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd',
        Matrix.mul_nonsing_inv_cancel_left _ _ hd']
    rw [← key, hA, Matrix.mul_zero, Matrix.zero_mul]
  · have hBJ : J * A * (H'⁻¹ * Jᴴ * H) * J = J * A := by
      rw [Matrix.mul_assoc, hPJ, Matrix.mul_one]
    exact matrix_exp_smul_mul_eq_mul_exp_smul_of_intertwine n n' _ J A hBJ t
  · have hB : (J * A * (H'⁻¹ * Jᴴ * H)) *ᵥ x = 0 := by
      have hfac : J * A * (H'⁻¹ * Jᴴ * H) = (J * A * H'⁻¹) * (Jᴴ * H) := by
        simp only [Matrix.mul_assoc]
      rw [hfac, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
    apply exp_mulVec_of_mulVec_eq_zero
    rw [Matrix.smul_mulVec, hB, smul_zero]
end GlobalTheory.CompanionTheory.IsometricMatrix
