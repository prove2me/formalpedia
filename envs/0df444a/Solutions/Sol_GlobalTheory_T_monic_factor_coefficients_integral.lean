-- Prove2me | solution 1 for GlobalTheory.T.monic_factor_coefficients_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:13:59.376234+00:00
-- url     : https://prove2.me/submissions/3a5deb5e-fcbc-4c0d-a92a-f1895b72c2fb

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MonicFactorCoefficientsIntegral
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MonicFactorCoefficientsIntegralStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_IntFac_isIntegral_coeff_of_shifted_product


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A : Type) [CommRing A] [Algebra ℂ A] (P Q : Polynomial A) (c₁ c₂ : ℂ), P.Monic → Q.Monic → (∀ u : ℂ, IsIntegral ℂ (P.eval (algebraMap ℂ A (u + c₁)) * Q.eval (algebraMap ℂ A (u + c₂)))) → ∀ k, IsIntegral ℂ (P.coeff k) ∧ IsIntegral ℂ (Q.coeff k) := by
  first | exact @GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_shifted_product | exact GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_shifted_product | (intros; apply GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_shifted_product <;> assumption)
end _root_.GlobalTheory.T
