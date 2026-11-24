-- Prove2me | solution 1 for GlobalTheory.T.exists_unit_frobenius_iterate_product_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:08:10.078045+00:00
-- url     : https://prove2.me/submissions/59ef5826-5148-426b-b109-cbf1bcc8049b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitFrobeniusIterateProductEq
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitFrobeniusIterateProductEqStatement
import Theorems.Thm_GlobalTheory_FrobeniusProduct_exists_unit_iterate_mul_eq


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
theorem _root_.solution : ∀ (A : Type) [CommRing A] (p : ℕ), IsAdicComplete (Ideal.span {(p : A)}) A → ∀ (φ : A →+* A) (u : A), IsUnit u → (∀ r : ℕ, ∃ M : ℕ, ∀ m ≥ M, (⇑φ)^[m] u - 1 ∈ Ideal.span {(p : A)} ^ r) → ∀ n : ℕ, 0 < n → ∃ c : A, IsUnit c ∧ (⇑φ)^[n] c * (⇑φ)^[n - 1] u = c := by
  first | exact @GlobalTheory.FrobeniusProduct.exists_unit_iterate_mul_eq | exact GlobalTheory.FrobeniusProduct.exists_unit_iterate_mul_eq | (intros; apply GlobalTheory.FrobeniusProduct.exists_unit_iterate_mul_eq <;> assumption)
end _root_.GlobalTheory.T
