-- Prove2me | solution 1 for GlobalTheory.T.prod_eq_sum_of_factorwise_linear_expansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:24:55.598789+00:00
-- url     : https://prove2.me/submissions/94266325-82a7-4970-8875-f0ea336f378d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ProdEqSumOfFactorwiseLinearExpansion
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ProdEqSumOfFactorwiseLinearExpansionStatement
import Theorems.Thm_GlobalTheory_prod_eq_sum_of_factorwise_expansion


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
theorem _root_.solution : ∀ (K : Type) [Fintype K] (X : K → Type) (I : Type) (S : Finset I) (x : I → ℂ) (a : ∀ n, I → X n → ℂ) (b : K → I → ℂ) (A : ∀ n, X n → ℂ) (B : K → ℂ), (∀ n (y : I → ℂ), (∀ q, ∑ i ∈ S, y i * a n i q = 0) → ∑ i ∈ S, y i * b n i = 0) → (∀ n (y : I → ℂ), (∀ q, A n q = ∑ i ∈ S, y i * a n i q) → B n = ∑ i ∈ S, y i * b n i) → (∀ q : ∀ n, X n, ∏ n, A n (q n) = ∑ i ∈ S, x i * ∏ n, a n i (q n)) → (∀ n, Nonempty (X n)) → ∏ n, B n = ∑ i ∈ S, x i * ∏ n, b n i := by
  first | exact @GlobalTheory.prod_eq_sum_of_factorwise_expansion | exact GlobalTheory.prod_eq_sum_of_factorwise_expansion | (intros; apply GlobalTheory.prod_eq_sum_of_factorwise_expansion <;> assumption)
end _root_.GlobalTheory.T
