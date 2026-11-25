-- Prove2me | solution 1 for GlobalTheory.T.polynomial_approx_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:26:21.541328+00:00
-- url     : https://prove2.me/submissions/126c938a-55df-4b19-b371-12a4dd909502

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PolynomialApproxUniqueness
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PolynomialApproxUniquenessStatement
import Theorems.Thm_GlobalTheory_coeff_mem_pow_of_flat_of_indep_mod_max


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] (φ : A →+* R), φ.Flat → (maximalIdeal A).map φ = maximalIdeal R → ∀ (θ : R) (q : Polynomial A), q.Monic → (q.map φ).eval θ = 0 → (∀ (n : ℕ) (r : R), ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R ^ n) → (∀ P : Polynomial A, P.natDegree < q.natDegree → (P.map φ).eval θ ∈ maximalIdeal R → ∀ i, P.coeff i ∈ maximalIdeal A) → ∀ (n : ℕ) (P : Polynomial A), P.natDegree < q.natDegree → (P.map φ).eval θ ∈ maximalIdeal R ^ n → ∀ i, P.coeff i ∈ maximalIdeal A ^ n := by
  first | exact @GlobalTheory.coeff_mem_pow_of_flat_of_indep_mod_max | exact GlobalTheory.coeff_mem_pow_of_flat_of_indep_mod_max | (intros; apply GlobalTheory.coeff_mem_pow_of_flat_of_indep_mod_max <;> assumption)
end _root_.GlobalTheory.T
