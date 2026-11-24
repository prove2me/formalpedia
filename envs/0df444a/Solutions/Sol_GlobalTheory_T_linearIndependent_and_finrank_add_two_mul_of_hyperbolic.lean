-- Prove2me | solution 1 for GlobalTheory.T.linearIndependent_and_finrank_add_two_mul_of_hyperbolic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:59:38.435269+00:00
-- url     : https://prove2.me/submissions/bdae2b09-0509-44b8-9b30-e3500aaca2b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FinrankAddTwoMulOfHyperbolicPairs
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FinrankAddTwoMulOfHyperbolicPairsStatement
import Theorems.Thm_GlobalTheory_finrank_add_two_mul_of_hyperbolic_pairs


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
theorem _root_.solution : ∀ (E V : Type) [Field E] [StarRing E] [AddCommGroup V] [Module E V] [FiniteDimensional E V] (h : V →ₗ⋆[E] V →ₗ[E] E), h.IsSymm → ∀ (W : Submodule E V) (i : ℕ) (e f : Fin i → V), (∀ a b, h (e a) (e b) = 0) → (∀ a b, h (f a) (f b) = 0) → (∀ a b, h (f a) (e b) = if a = b then 1 else 0) → (∀ a, ∀ x ∈ W, h x (e a) = 0 ∧ h x (f a) = 0) → W ⊔ Submodule.span E (Set.range e ∪ Set.range f) = ⊤ → LinearIndependent E e ∧ Module.finrank E W + 2 * i = Module.finrank E V := by
  first | exact @GlobalTheory.finrank_add_two_mul_of_hyperbolic_pairs | exact GlobalTheory.finrank_add_two_mul_of_hyperbolic_pairs | (intros; apply GlobalTheory.finrank_add_two_mul_of_hyperbolic_pairs <;> assumption)
end _root_.GlobalTheory.T
