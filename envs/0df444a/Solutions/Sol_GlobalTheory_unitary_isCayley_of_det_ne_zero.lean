-- Prove2me | solution 1 for GlobalTheory.unitary_isCayley_of_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:39:44.064802+00:00
-- url     : https://prove2.me/submissions/d611d080-3701-46c1-a1e1-4418f272a018

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UnitaryFamilyEqCayleyOfSkewFamily
import Theorems.Thm_GlobalTheory_cayleyInv_one_sub
import Theorems.Thm_GlobalTheory_cayleyInv_one_add
import Theorems.Thm_GlobalTheory_cayleyInv_det_one_sub
import Theorems.Thm_GlobalTheory_cayleyInv_skew

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open GlobalTheory
variable {n : ℕ}
namespace GlobalTheory
theorem _root_.solution : ∀ (L : Type) [Field L] [NumberField L] (n : ℕ)
    (X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ),
    (∀ σ, X σ * (X (ComplexEmbedding.conjugate σ))ᵀ = 1) → (∀ σ, (1 + X σ).det ≠ 0) →
    ∃ Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, (∀ σ, Y (ComplexEmbedding.conjugate σ) = -(Y σ)ᵀ) ∧
      (∀ σ, (1 - Y σ).det ≠ 0) ∧ ∀ σ, (1 + Y σ) * (1 - Y σ)⁻¹ = X σ := by
  intro L _ _ n X hX hdet
  have hu : ∀ σ, IsUnit (X σ + 1).det := fun σ => by
    rw [add_comm]; exact isUnit_iff_ne_zero.mpr (hdet σ)
  refine ⟨fun σ => (X σ - 1) * (X σ + 1)⁻¹, fun σ => ?_, fun σ => ?_, fun σ => ?_⟩
  · exact cayleyInv_skew (X σ) (X (ComplexEmbedding.conjugate σ)) (hX σ) (hu σ) (hu _)
  · exact isUnit_iff_ne_zero.mp (cayleyInv_det_one_sub (X σ) (hu σ))
  · show (1 + (X σ - 1) * (X σ + 1)⁻¹) * (1 - (X σ - 1) * (X σ + 1)⁻¹)⁻¹ = X σ
    have hY := cayleyInv_det_one_sub (X σ) (hu σ)
    rw [cayleyInv_one_add _ (hu σ), ← cayleyInv_one_sub _ (hu σ), Matrix.mul_assoc,
      mul_nonsing_inv _ hY, Matrix.mul_one]
end GlobalTheory
