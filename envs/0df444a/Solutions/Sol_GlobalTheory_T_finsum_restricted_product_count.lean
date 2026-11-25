-- Prove2me | solution 1 for GlobalTheory.T.finsum_restricted_product_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:24:09.866271+00:00
-- url     : https://prove2.me/submissions/95f9380a-2809-41e2-9efa-b6f227ac1454

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumRestrictedProductCount
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumRestrictedProductCountStatement
import Theorems.Thm_GlobalTheory_finsum_finprod_mul_two_pow_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter
open scoped Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (I R : Type) (D : I → Type) (S : Set I) (B : ∀ i, D i → ℂ) (ℓ : R → ∀ i, D i) (A : Set R) (k m : ℕ), (∀ i, Nonempty (D i)) → (∀ i ∈ S, (Function.support (B i)).Finite) → (∀ᶠ i in cofinite, ∃ u : D i, ∀ d, B i d = if d = u then 1 else 0) → (∀ c ∈ A, ∀ᶠ i in cofinite, B i (ℓ c i) = 1) → (∀ e : ∀ i, D i, (∀ i ∈ S, B i (e i) ≠ 0) → Nat.card {c : R // c ∈ A ∧ ∀ i ∈ S, ℓ c i = e i} * 2 ^ k = 2 ^ m) → (∑ᶠ c : R, if c ∈ A then ∏ᶠ i ∈ S, B i (ℓ c i) else 0) * (2 : ℂ) ^ k = (2 : ℂ) ^ m * ∏ᶠ i ∈ S, ∑ᶠ d, B i d := by
  first | exact @GlobalTheory.finsum_finprod_mul_two_pow_eq | exact GlobalTheory.finsum_finprod_mul_two_pow_eq | (intros; apply GlobalTheory.finsum_finprod_mul_two_pow_eq <;> assumption)
end _root_.GlobalTheory.T
