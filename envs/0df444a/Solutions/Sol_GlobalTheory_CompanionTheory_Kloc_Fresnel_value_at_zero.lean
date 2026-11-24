-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Kloc.Fresnel.value_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:05:36.456024+00:00
-- url     : https://prove2.me/submissions/07e7b91f-02c3-4563-8563-4f839df579ce

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierTransformMatrixSpaceInvolution
import Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_exists_chain
import Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_exists_scale
import Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_opE_comp
import Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_chE_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Kloc GlobalTheory.CompanionTheory.Kloc.Fresnel
variable {m n : ℕ}
namespace GlobalTheory.CompanionTheory.Kloc.Fresnel
theorem _root_.solution : ∀ (m n : ℕ) (C s : ℂ) (k : ℝ), C ≠ 0 → k ≠ 0 → ‖s‖ = 2 * |k| → ∃ c : ℂ, c ≠ 0 ∧ ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, (fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => C * ∫ v : Fin m → Fin n → ℂ, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => C * ∫ v : Fin m → Fin n → ℂ, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => C * ∫ v : Fin m → Fin n → ℂ, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of u)) * g u) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => C * ∫ v : Fin m → Fin n → ℂ, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of u)) * g u) ⇑φ))))) 0 = c * ∫ v : Fin m → Fin n → ℂ, φ v := by
  intro m n C s k hC hk hs
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, norm_zero] at hs
    have := abs_pos.2 hk
    linarith
  have hn : ‖s‖ ≠ 0 := norm_ne_zero_iff.2 hs0
  have hω : ‖s / ‖s‖‖ = 1 := by
    rw [norm_div, Complex.norm_real, norm_norm, div_self hn]
  obtain ⟨κ, hκ0, hκ⟩ := exists_scale m n
  have hCκ : C * κ ≠ 0 := mul_ne_zero hC (by exact_mod_cast hκ0.ne')
  obtain ⟨c, hc0, hc⟩ := exists_chain (V := EuclideanSpace ℂ (Fin m × Fin n)) (C * κ) k ‖s‖ hCκ hk hs
    (unitMul (Fin m × Fin n) (s / ‖s‖) hω)
  have hκC : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ0.ne'
  refine ⟨c * (κ : ℂ)⁻¹, mul_ne_zero hc0 (inv_ne_zero hκC), fun φ => ?_⟩
  obtain ⟨φ', hφ⟩ : ∃ φ' : 𝓢(EuclideanSpace ℂ (Fin m × Fin n), ℂ), ⇑φ = ⇑φ' ∘ matEquiv m n :=
    ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (matEquiv m n).symm φ, by
      funext u; simp⟩
  change opE C s (opE C s (opE C s (chE k (opE C s (chE k ⇑φ))))) 0 = _
  have hR : ∫ v : Fin m → Fin n → ℂ, φ v = κ * ∫ y, φ' y := by
    rw [← hκ (fun y => φ' y)]
    simp [hφ]
  rw [hR, hφ, chE_comp, opE_comp C s hs0 hω κ hκ, chE_comp, opE_comp C s hs0 hω κ hκ,
    opE_comp C s hs0 hω κ hκ, opE_comp C s hs0 hω κ hκ, Function.comp_apply, map_zero, hc φ']
  field_simp
end GlobalTheory.CompanionTheory.Kloc.Fresnel
