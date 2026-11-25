-- Prove2me | solution 1 for GlobalTheory.FreeQuotient.isFreeRingAction_of_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:49:36.666484+00:00
-- url     : https://prove2.me/submissions/2cd95059-ab98-4529-8352-999117f793ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.FreeQuotient
variable (G : Type*) [Group G] (A : Type*) [CommRing A] [MulSemiringAction G A]
namespace GlobalTheory.FreeQuotient
theorem _root_.solution (K : Type*) [Field K] [MulSemiringAction G K]
    [FaithfulSMul G K] : IsFreeRingAction G K := by
  intro g hg
  rcases Ideal.eq_bot_or_top (Ideal.span (Set.range fun a : K ↦ g • a - a)) with h | h
  · refine absurd (eq_of_smul_eq_smul (α := K) fun a ↦ ?_) hg
    have : g • a - a ∈ Ideal.span (Set.range fun a : K ↦ g • a - a) := Ideal.subset_span ⟨a, rfl⟩
    rw [h, Ideal.mem_bot, sub_eq_zero] at this
    rw [this, one_smul]
  · exact h
end GlobalTheory.FreeQuotient
