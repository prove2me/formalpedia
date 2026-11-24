-- Prove2me | solution 1 for GlobalTheory.QuadraticZeta.absNorm_mul_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:45:40.009722+00:00
-- url     : https://prove2.me/submissions/168ca6f5-8b9c-4fe8-aa8e-9899829d85e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Theorems.Thm_GlobalTheory_QuadraticZeta_exists_basis_embedding
import Theorems.Thm_GlobalTheory_QuadraticZeta_det_mul_im

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
theorem _root_.solution (I : FractionalIdeal (𝓞 K)⁰ K)
    (bI : Basis (Fin 2) ℤ (I : Submodule (𝓞 K) K)) :
    (absNorm I : ℝ) * (√d / 2) = |(σ (bI 1) * conj (σ (bI 0))).im| := by
  obtain ⟨b, t, h0, -, hi⟩ := exists_basis_embedding h2 hD σ
  let b' : Basis (Fin 2) ℚ K := b.localizationLocalization ℚ ℤ⁰ K
  have e0 : b' 0 = 1 := by simp [b', h0]
  have e1 : b' 1 = b 1 := by simp [b']
  rw [← det_mul_im σ b' e0, ← abs_det_basis_change b I bI, abs_mul, e1, ← hi,
    show 4 * (σ (b 1)).im ^ 2 = (2 * (σ (b 1)).im) ^ 2 by ring, Real.sqrt_sq_eq_abs, abs_mul,
    show Subtype.val ∘ bI = ![(bI 0 : K), bI 1] by ext i; fin_cases i <;> rfl]
  push_cast
  rw [abs_two]
  ring
end GlobalTheory.QuadraticZeta
