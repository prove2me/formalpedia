-- Prove2me | solution 1 for GlobalTheory.SW.symplectic_eq_parabolic_J_parabolic_J_parabolic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:45:34.560742+00:00
-- url     : https://prove2.me/submissions/a89bb7f9-9575-462e-b97f-fd3ba99ae0af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticEqParabolicJParabolicJParabolic
import Theorems.Thm_GlobalTheory_SW_unip_mem_symplecticGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open private exists_symmetric_X_isUnit_det_add_mul_of_symplectic from Mathlib.LinearAlgebra.SymplecticGroup
open GlobalTheory GlobalTheory.SW
namespace GlobalTheory.SW
theorem _root_.solution :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → ∃ p₁ ∈ Matrix.symplecticGroup ι ℚ, ∃ p₂ ∈ Matrix.symplecticGroup ι ℚ, ∃ p₃ ∈ Matrix.symplecticGroup ι ℚ, p₁.toBlocks₂₁ = 0 ∧ p₂.toBlocks₂₁ = 0 ∧ p₃.toBlocks₂₁ = 0 ∧ σ = p₁ * Matrix.J ι ℚ * p₂ * Matrix.J ι ℚ * p₃ := by
  intro ι _ _ σ hσ
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, σ = fromBlocks A B C D :=
    ⟨_, _, _, _, σ.fromBlocks_toBlocks.symm⟩
  obtain ⟨X, hX, hu⟩ := exists_symmetric_X_isUnit_det_add_mul_of_symplectic hσ
  have hb := (SymplecticGroup.fromBlocks_mem_iff.1 hσ).1
  have h1 : (A + X * C)ᵀ * C = Cᵀ * (A + X * C) := by
    rw [transpose_add, transpose_mul, hX.eq, add_mul, mul_add, hb, Matrix.mul_assoc]
  generalize hc : A + X * C = c at hu h1
  have hcT : IsUnit cᵀ.det := by rwa [det_transpose]
  have hY : (C * c⁻¹).IsSymm := by
    unfold Matrix.IsSymm
    rw [transpose_mul, transpose_nonsing_inv]
    calc cᵀ⁻¹ * Cᵀ = cᵀ⁻¹ * (Cᵀ * c) * c⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
      _ = C * c⁻¹ := by rw [← h1, nonsing_inv_mul_cancel_left _ _ hcT]
  have hY' : C * c⁻¹ * c = C := nonsing_inv_mul_cancel_right _ _ hu
  generalize C * c⁻¹ = Y at hY hY'
  have hJ := SymplecticGroup.J_mem ι ℚ
  refine ⟨fromBlocks 1 (-X) 0 1, unip_mem_symplecticGroup hX.neg,
    fromBlocks 1 (-Y) 0 1, unip_mem_symplecticGroup hY.neg,
    J ι ℚ * fromBlocks 1 Y 0 1 * J ι ℚ * fromBlocks 1 X 0 1 * fromBlocks A B C D,
    mul_mem (mul_mem (mul_mem (mul_mem hJ (unip_mem_symplecticGroup hY)) hJ)
      (unip_mem_symplecticGroup hX)) hσ, by simp, by simp, ?_, ?_⟩
  · rw [Matrix.mul_assoc _ _ (fromBlocks A B C D), fromBlocks_multiply]
    simp only [Matrix.one_mul, hc]
    simp [J, fromBlocks_multiply, hY']
  · have e1 : (fromBlocks 1 (-Y) 0 1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) * fromBlocks 1 Y 0 1 = 1 := by
      simp [fromBlocks_multiply]
    have e2 : (fromBlocks 1 (-X) 0 1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) * fromBlocks 1 X 0 1 = 1 := by
      simp [fromBlocks_multiply]
    have e3 := J_squared ι ℚ
    generalize (fromBlocks 1 (-Y) 0 1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) = y' at e1 ⊢
    generalize (fromBlocks 1 Y 0 1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) = y at e1 ⊢
    generalize (fromBlocks 1 (-X) 0 1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) = x' at e2 ⊢
    generalize (fromBlocks 1 X 0 1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) = x at e2 ⊢
    generalize fromBlocks A B C D = s
    generalize J ι ℚ = j at e3 ⊢
    have e4 : ∀ m, j * (j * m) = -m := fun m => by rw [← mul_assoc, e3, neg_one_mul]
    have e5 : ∀ m, y' * (y * m) = m := fun m => by rw [← mul_assoc, e1, one_mul]
    have e6 : ∀ m, x' * (x * m) = m := fun m => by rw [← mul_assoc, e2, one_mul]
    simp only [mul_assoc, e4, mul_neg, e5, neg_neg, e6]
end GlobalTheory.SW
