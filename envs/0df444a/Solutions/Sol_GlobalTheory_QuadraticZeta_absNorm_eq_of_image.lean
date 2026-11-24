-- Prove2me | solution 1 for GlobalTheory.QuadraticZeta.absNorm_eq_of_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:01:30.011976+00:00
-- url     : https://prove2.me/submissions/fb79fa4e-dacd-4fc4-a1e9-4cf7b366e926

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Theorems.Thm_GlobalTheory_QuadraticZeta_discr_pos
import Theorems.Thm_GlobalTheory_QuadraticZeta_absNorm_mul_sqrt
import Theorems.Thm_GlobalTheory_QuadraticZeta_exists_basis_of_image

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal
open scoped nonZeroDivisors UpperHalfPlane ComplexConjugate
open GlobalTheory GlobalTheory.QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}
variable (h2 : finrank ℚ K = 2) (hD : discr K = -d) (σ : K →+* ℂ)
include h2 hD
namespace GlobalTheory.QuadraticZeta
theorem _root_.solution {𝔞 : FractionalIdeal (𝓞 K)⁰ K} {ω : ℂ} {τ : ℍ} (hω : ω ≠ 0)
    (h : ∀ z, z ∈ σ '' 𝔞 ↔ ∃ m n : ℤ, ω * (m * (τ : ℂ) + n) = z) :
    (absNorm 𝔞 : ℝ) = 2 * ‖ω‖ ^ 2 * τ.im / √d := by
  obtain ⟨b, e0, e1⟩ := exists_basis_of_image σ hω h
  have := absNorm_mul_sqrt h2 hD σ 𝔞 b
  have hd := discr_pos h2 hD
  have hy := τ.im_pos
  rw [e0, e1, show (ω * conj (ω * τ)).im = -(‖ω‖ ^ 2 * τ.im) by
    simp [Complex.sq_norm, Complex.normSq_apply]; ring, abs_neg,
    abs_of_nonneg (by positivity)] at this
  field_simp
  linarith
end GlobalTheory.QuadraticZeta
