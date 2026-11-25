-- Prove2me | solution 1 for GlobalTheory.T.fourier_injective_matrix_space
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:19:29.5324+00:00
-- url     : https://prove2.me/submissions/cbae9b0e-b15b-4840-aa3c-f91f3bab4638

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierInjectiveMatrixSpace
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierInjectiveMatrixSpaceStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FourierMat_fourier_uniqueness


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (m n : ℕ) (s : ℂ), s ≠ 0 → ∀ g : (Fin m → Fin n → ℂ) → ℂ, Continuous g → Integrable g → (∀ u : Fin m → Fin n → ℂ, ∫ v, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v = 0) → g = 0 := by
  first | exact @GlobalTheory.CompanionTheory.FourierMat.fourier_uniqueness | exact GlobalTheory.CompanionTheory.FourierMat.fourier_uniqueness | (intros; apply GlobalTheory.CompanionTheory.FourierMat.fourier_uniqueness <;> assumption)
end _root_.GlobalTheory.T
