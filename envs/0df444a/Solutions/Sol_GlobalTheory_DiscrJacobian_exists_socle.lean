-- Prove2me | solution 1 for GlobalTheory.DiscrJacobian.exists_socle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:43:43.320818+00:00
-- url     : https://prove2.me/submissions/6ce879ca-78bf-48f0-8f1a-964c84e33fd2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrMulDetEqNormOfAnnihilator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsUnitDetOfProductMapNeZero
import Theorems.Thm_GlobalTheory_DiscrJacobian_mu_tmul
import Theorems.Thm_GlobalTheory_DiscrJacobian_der_tmul
import Theorems.Thm_GlobalTheory_DiscrJacobian_pairing_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.DiscrJacobian.mu_tmul
attribute [local simp] GlobalTheory.DiscrJacobian.der_tmul
attribute [local simp] GlobalTheory.DiscrJacobian.pairing_tmul

set_option autoImplicit false
open GlobalTheory GlobalTheory.DiscrJacobian
open scoped TensorProduct
variable {R B C : Type} [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
namespace GlobalTheory.DiscrJacobian
theorem _root_.solution {V : Type} [AddCommGroup V] [Module R V] (n : Ideal B) (φ : B →ₗ[R] V)
    (hφ : φ ≠ 0) (N : ℕ) (hN : ∀ w ∈ n ^ N, φ w = 0) :
    ∃ y, φ y ≠ 0 ∧ ∀ w ∈ n, φ (w * y) = 0 := by
  induction N with
  | zero => exact absurd (LinearMap.ext fun w => hN w (by simp)) hφ
  | succ N ih =>
    by_cases h : ∀ w ∈ n ^ N, φ w = 0
    · exact ih h
    · push Not at h
      obtain ⟨y, hy, hy'⟩ := h
      exact ⟨y, hy', fun w hw => hN _ (by rw [pow_succ']; exact Ideal.mul_mem_mul hw hy)⟩
end GlobalTheory.DiscrJacobian
