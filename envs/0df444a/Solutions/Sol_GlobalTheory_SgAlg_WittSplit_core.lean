-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittSplit.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:39:03.566634+00:00
-- url     : https://prove2.me/submissions/4f679836-bdd6-431f-b440-77e5590417e0

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittFreeTuplesSplitQuadraticEtale
import Theorems.Thm_GlobalTheory_SgAlg_WittSplit_exists_left_inv_unit
import Theorems.Thm_GlobalTheory_SgAlg_WittSplit_exists_right_inv_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SgAlg Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.SgAlg GlobalTheory.SgAlg.WittSplit
variable {F : Type} [Field F] {m k : Type} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
namespace GlobalTheory.SgAlg.WittSplit
theorem _root_.solution (u u' : Matrix m k F) (φ φ' : Matrix k m F) (hu : ∃ L : Matrix k m F, L * u = 1)
    (hu' : ∃ L : Matrix k m F, L * u' = 1) (hφ : ∃ ψ : Matrix m k F, φ * ψ = 1)
    (hφ' : ∃ ψ : Matrix m k F, φ' * ψ = 1) (h : φ * u = φ' * u') :
    ∃ A : Matrix m m F, IsUnit A.det ∧ A * u = u' ∧ φ' * A = φ := by
  obtain ⟨L, hL, hLu'⟩ := exists_left_inv_unit u u' hu hu'
  set B : Matrix m m F := 1 + (u' - u) * L with hBdef
  have hBu : B * u = u' := by
    rw [hBdef, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hL, Matrix.mul_one]; abel
  have hB : IsUnit B.det := by
    have : B.det = (L * u').det := by
      rw [hBdef, Matrix.det_one_add_mul_comm]; congr 1; rw [Matrix.mul_sub, hL]; abel
    rw [this]; exact hLu'
  clear_value B
  obtain ⟨ψ0, hψ0⟩ := hφ
  have hBB : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB
  have hφ1 : ∃ ψ : Matrix m k F, φ * B⁻¹ * ψ = 1 := ⟨B * ψ0, by rw [Matrix.mul_assoc φ, ← Matrix.mul_assoc B⁻¹, hBB, Matrix.one_mul, hψ0]⟩
  obtain ⟨ψ, hψ, hψu⟩ := exists_right_inv_unit (φ * B⁻¹) φ' hφ1 hφ'
  have h1u' : φ * B⁻¹ * u' = φ' * u' := by
    conv_lhs => rw [← hBu]
    rw [show φ * B⁻¹ * (B * u) = φ * (B⁻¹ * B) * u by simp only [Matrix.mul_assoc], hBB, Matrix.mul_one, h]
  refine ⟨(1 + ψ * (φ * B⁻¹ - φ')) * B, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul]
    refine IsUnit.mul ?_ hB
    rw [Matrix.det_one_add_mul_comm]
    have : 1 + (φ * B⁻¹ - φ') * ψ = φ * B⁻¹ * ψ := by rw [Matrix.sub_mul, hψ]; abel
    rw [this]; exact hψu
  · rw [Matrix.mul_assoc, hBu, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.sub_mul, h1u',
      sub_self, Matrix.mul_zero, add_zero]
  · rw [← Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hψ, Matrix.one_mul,
      add_sub_cancel, Matrix.mul_assoc, hBB, Matrix.mul_one]
end GlobalTheory.SgAlg.WittSplit
