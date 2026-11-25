-- Prove2me | solution 1 for GlobalTheory.T.fourier_transform_matrix_space_involution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:19:44.329205+00:00
-- url     : https://prove2.me/submissions/1f6d6d9f-1395-47e9-b3e9-1bc3e9b9582f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierTransformMatrixSpaceInvolution
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierTransformMatrixSpaceInvolutionStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_value_at_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (m n : ℕ) (C s : ℂ) (k : ℝ), C ≠ 0 → k ≠ 0 → ‖s‖ = 2 * |k| → ∃ c : ℂ, c ≠ 0 ∧ ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, (fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => C * ∫ v : Fin m → Fin n → ℂ, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => C * ∫ v : Fin m → Fin n → ℂ, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => C * ∫ v : Fin m → Fin n → ℂ, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of u)) * g u) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => C * ∫ v : Fin m → Fin n → ℂ, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of u)) * g u) ⇑φ))))) 0 = c * ∫ v : Fin m → Fin n → ℂ, φ v := by
  first | exact @GlobalTheory.CompanionTheory.Kloc.Fresnel.value_at_zero | exact GlobalTheory.CompanionTheory.Kloc.Fresnel.value_at_zero | (intros; apply GlobalTheory.CompanionTheory.Kloc.Fresnel.value_at_zero <;> assumption)
end _root_.GlobalTheory.T
