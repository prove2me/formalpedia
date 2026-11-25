-- Prove2me | solution 1 for GlobalTheory.T.exists_linearIndependent_products_function_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:16:17.890846+00:00
-- url     : https://prove2.me/submissions/499e745e-64ee-4f35-9a1e-6a7e3e2d4c04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ManyIndependentProductsInFunctionField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ManyIndependentProductsInFunctionFieldStatement
import Theorems.Thm_GlobalTheory_many_independent_products_in_function_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin D → K), IsTranscendenceBasis ℤ x → ∀ (J : Type) [Fintype J] (e : J → K), LinearIndependent ℤ e → ∀ m : ℕ, 0 < m → ∃ v : Fin (Fintype.card J * m ^ D) → K, LinearIndependent ℤ v ∧ ∀ s, ∃ (u : Fin m → J) (a : Fin D → ℕ), (∀ i, a i < m) ∧ v s = (∏ l, e (u l)) * ∏ i, x i ^ a i := by
  first | exact @GlobalTheory.many_independent_products_in_function_field | exact GlobalTheory.many_independent_products_in_function_field | (intros; apply GlobalTheory.many_independent_products_in_function_field <;> assumption)
end _root_.GlobalTheory.T
