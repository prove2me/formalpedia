-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QuadChirp.exists_schwartz_chirp_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:52:03.336518+00:00
-- url     : https://prove2.me/submissions/15ca91c2-ee79-4102-ad3b-2f4e365e3882

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchwartzQuadraticPhaseMultiplication
import Theorems.Thm_GlobalTheory_CompanionTheory_QuadChirp_chirp_hasTemperateGrowth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix SchwartzMap ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QuadChirp
namespace GlobalTheory.CompanionTheory.QuadChirp
theorem _root_.solution :
    ∀ (m n : ℕ) (k : ℝ) (b : Matrix (Fin n) (Fin n) ℂ), bᴴ = b →
      ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∃ ψ : SchwartzMap (Fin m → Fin n → ℂ) ℂ,
        ⇑ψ = fun u => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) *
          Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) * φ u := by
  intro m n k b hb φ
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun u : Fin m → Fin n → ℂ => Complex.exp (2 * Real.pi *
    Complex.I * (k : ℂ) * Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u)))) φ, ?_⟩
  funext u
  rw [SchwartzMap.smulLeftCLM_apply_apply (GlobalTheory.CompanionTheory.QuadChirp.chirp_hasTemperateGrowth k b hb), smul_eq_mul]
end GlobalTheory.CompanionTheory.QuadChirp
