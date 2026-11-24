-- Prove2me | solution 1 for GlobalTheory.T.unitary_family_eq_cayley_of_skew_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:46:19.466679+00:00
-- url     : https://prove2.me/submissions/47141ae9-669f-4fc5-b3c6-3f49e3a5e630

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UnitaryFamilyEqCayleyOfSkewFamily
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UnitaryFamilyEqCayleyOfSkewFamilyStatement
import Theorems.Thm_GlobalTheory_unitary_isCayley_of_det_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ), (∀ σ, X σ * (X (ComplexEmbedding.conjugate σ))ᵀ = 1) → (∀ σ, (1 + X σ).det ≠ 0) → ∃ Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, (∀ σ, Y (ComplexEmbedding.conjugate σ) = -(Y σ)ᵀ) ∧ (∀ σ, (1 - Y σ).det ≠ 0) ∧ ∀ σ, (1 + Y σ) * (1 - Y σ)⁻¹ = X σ := by
  first | exact @GlobalTheory.unitary_isCayley_of_det_ne_zero | exact GlobalTheory.unitary_isCayley_of_det_ne_zero | (intros; apply GlobalTheory.unitary_isCayley_of_det_ne_zero <;> assumption)
end _root_.GlobalTheory.T
