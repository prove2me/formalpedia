-- Prove2me | solution 1 for GlobalTheory.T.polynomial_approx_pow_maximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:26:18.724346+00:00
-- url     : https://prove2.me/submissions/8a051f51-7b3f-4464-a4e7-c47417e33e47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PolynomialApproxPowMaximal
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PolynomialApproxPowMaximalStatement
import Theorems.Thm_GlobalTheory_exists_poly_sub_mem_maximalIdeal_pow


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
theorem _root_.solution : ∀ {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] (φ : A →+* R), (maximalIdeal A).map φ = maximalIdeal R → ∀ θ : R, (∀ r : R, ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R) → ∀ (n : ℕ) (r : R), ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R ^ n := by
  first | exact @GlobalTheory.exists_poly_sub_mem_maximalIdeal_pow | exact GlobalTheory.exists_poly_sub_mem_maximalIdeal_pow | (intros; apply GlobalTheory.exists_poly_sub_mem_maximalIdeal_pow <;> assumption)
end _root_.GlobalTheory.T
