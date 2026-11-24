-- Prove2me | solution 1 for GlobalTheory.T.not_dvd_coeff_aeval_one_add_X_pow_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:35:26.066182+00:00
-- url     : https://prove2.me/submissions/7ea373ea-8678-4a81-b55e-48e7bdf4a97f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotDvdCoeffAevalOneAddXPowSubOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotDvdCoeffAevalOneAddXPowSubOneStatement
import Theorems.Thm_GlobalTheory_not_dvd_coeff_aeval_oneAddX_pow_sub_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (σ : Type) [Fintype σ] (l μ : ℕ), l.Prime → ϖ ∣ (l : O) → ∀ (F : MvPolynomial σ O) (e : σ → ℕ) (m₀ : σ →₀ ℕ), (∀ m : σ →₀ ℕ, m.degree ≤ ∑ q, m₀ q * l ^ e q → ϖ ^ μ ∣ F.coeff m) → ¬ ϖ ^ (μ + 1) ∣ F.coeff m₀ → (∀ m : σ →₀ ℕ, m ≠ m₀ → ∑ q, m q * l ^ e q ≤ ∑ q, m₀ q * l ^ e q → ϖ ^ (μ + 1) ∣ F.coeff m) → ¬ ϖ ^ (μ + 1) ∣ (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial O) ^ (l ^ e q) - 1) F).coeff (∑ q, m₀ q * l ^ e q) := by
  first | exact @GlobalTheory.not_dvd_coeff_aeval_oneAddX_pow_sub_one | exact GlobalTheory.not_dvd_coeff_aeval_oneAddX_pow_sub_one | (intros; apply GlobalTheory.not_dvd_coeff_aeval_oneAddX_pow_sub_one <;> assumption)
end _root_.GlobalTheory.T
