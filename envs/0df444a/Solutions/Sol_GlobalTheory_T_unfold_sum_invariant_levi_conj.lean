-- Prove2me | solution 1 for GlobalTheory.T.unfold_sum_invariant_levi_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:46:18.838795+00:00
-- url     : https://prove2.me/submissions/7a8f39f8-a277-4b32-8ebe-b492a2b92efe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnfoldSumInvariantLeviConj
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnfoldSumInvariantLeviConjStatement
import Theorems.Thm_GlobalTheory_unfold_sum_conj_invariant


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
theorem _root_.solution : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ F : P → ℂ, (∀ k ∈ KP, ∀ x, F (k⁻¹ * x * k) = F x) → ∀ k ∈ KM, ∀ y : P, (∑ᶠ x : N ⧸ L, F ((u (Quotient.out x))⁻¹ * ((s k)⁻¹ * y * s k) * u (Quotient.out x))) = ∑ᶠ x : N ⧸ L, F ((u (Quotient.out x))⁻¹ * y * u (Quotient.out x)) := by
  first | exact @GlobalTheory.unfold_sum_conj_invariant | exact GlobalTheory.unfold_sum_conj_invariant | (intros; apply GlobalTheory.unfold_sum_conj_invariant <;> assumption)
end _root_.GlobalTheory.T
