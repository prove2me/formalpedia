-- Prove2me | solution 1 for GlobalTheory.T.linear_map_short_exact_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:46:25.033687+00:00
-- url     : https://prove2.me/submissions/0ca09bfd-6226-4066-b1c3-c73649eae4bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_LinearMapShortExactCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_LinearMapShortExactCommuteStatement
import Theorems.Thm_GlobalTheory_trace_eq_add_of_shortExact


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
theorem _root_.solution : ∀ (K : Type) [Field K] (U : Type) [AddCommGroup U] [Module K U] [FiniteDimensional K U] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (i : U →ₗ[K] V) (p : V →ₗ[K] W) (a : U →ₗ[K] U) (b : V →ₗ[K] V) (c : W →ₗ[K] W), Function.Injective i → Function.Surjective p → LinearMap.range i = LinearMap.ker p → b ∘ₗ i = i ∘ₗ a → p ∘ₗ b = c ∘ₗ p → LinearMap.trace K V b = LinearMap.trace K U a + LinearMap.trace K W c := by
  first | exact @GlobalTheory.trace_eq_add_of_shortExact | exact GlobalTheory.trace_eq_add_of_shortExact | (intros; apply GlobalTheory.trace_eq_add_of_shortExact <;> assumption)
end _root_.GlobalTheory.T
