-- Prove2me | solution 1 for GlobalTheory.T.schwartz_quadratic_phase_multiplication
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:24:22.073292+00:00
-- url     : https://prove2.me/submissions/32406842-4f54-4847-8fde-cfd7b46c4362

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchwartzQuadraticPhaseMultiplication
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchwartzQuadraticPhaseMultiplicationStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_QuadChirp_exists_schwartz_chirp_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix SchwartzMap
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (m n : ℕ) (k : ℝ) (b : Matrix (Fin n) (Fin n) ℂ), bᴴ = b → ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∃ ψ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ⇑ψ = fun u => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) * φ u := by
  first | exact @GlobalTheory.CompanionTheory.QuadChirp.exists_schwartz_chirp_mul | exact GlobalTheory.CompanionTheory.QuadChirp.exists_schwartz_chirp_mul | (intros; apply GlobalTheory.CompanionTheory.QuadChirp.exists_schwartz_chirp_mul <;> assumption)
end _root_.GlobalTheory.T
