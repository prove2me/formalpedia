-- Prove2me | solution 1 for GlobalTheory.QuadraticZeta.ne_zero_of_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:46:34.792402+00:00
-- url     : https://prove2.me/submissions/71d92833-a8f4-4579-9750-edae785ff9eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding

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
omit h2 hD
namespace GlobalTheory.QuadraticZeta
theorem _root_.solution {𝔞 : FractionalIdeal (𝓞 K)⁰ K} (h0 : 𝔞 ≠ 0) {ω : ℂ} {τ : ℍ}
    (h : ∀ z, z ∈ σ '' 𝔞 ↔ ∃ m n : ℤ, ω * (m * (τ : ℂ) + n) = z) : ω ≠ 0 := by
  rintro rfl
  refine h0 (eq_zero_iff.2 fun x hx => σ.injective ?_)
  obtain ⟨m, n, e⟩ := (h (σ x)).1 ⟨x, hx, rfl⟩
  simp [← e]
end GlobalTheory.QuadraticZeta
