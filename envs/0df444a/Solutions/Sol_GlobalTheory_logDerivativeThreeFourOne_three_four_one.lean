-- Prove2me | solution 1 for GlobalTheory.logDerivativeThreeFourOne.three_four_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:34:43.507819+00:00
-- url     : https://prove2.me/submissions/68abea7a-bad0-4378-b7ea-3029d88d82b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivativeBound
import Theorems.Thm_GlobalTheory_logDerivativeThreeFourOne_neg_logDeriv_eq
import Theorems.Thm_GlobalTheory_logDerivativeThreeFourOne_term_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.logDerivativeThreeFourOne
namespace GlobalTheory.logDerivativeThreeFourOne
theorem _root_.solution : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ t : ℝ), 1 < σ → 0 ≤ -(3 * (deriv (LFunction (1 : DirichletCharacter ℂ q)) σ / LFunction (1 : DirichletCharacter ℂ q) σ).re + 4 * (deriv (LFunction χ) (σ + t * I) / LFunction χ (σ + t * I)).re + (deriv (LFunction (χ ^ 2)) (σ + 2 * t * I) / LFunction (χ ^ 2) (σ + 2 * t * I)).re) := by
  intro q _ χ σ t hσ
  have h1 := neg_logDeriv_eq (1 : DirichletCharacter ℂ q) (s := (σ : ℂ)) (by simpa using hσ)
  have h2 := neg_logDeriv_eq χ (s := (σ : ℂ) + t * I) (by simpa using hσ)
  have h3 := neg_logDeriv_eq (χ ^ 2) (s := (σ : ℂ) + 2 * t * I) (by simpa using hσ)
  have h := ((h1.mul_left 3).add (h2.mul_left 4)).add h3
  have hnn := h.nonneg (fun n => term_nonneg χ σ t n)
  linarith
end GlobalTheory.logDerivativeThreeFourOne
