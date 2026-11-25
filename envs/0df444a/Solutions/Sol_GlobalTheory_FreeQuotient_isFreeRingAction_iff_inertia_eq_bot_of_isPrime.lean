-- Prove2me | solution 1 for GlobalTheory.FreeQuotient.isFreeRingAction_iff_inertia_eq_bot_of_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:49:28.534551+00:00
-- url     : https://prove2.me/submissions/15fddec7-c068-4a73-88ec-661c6a25deb3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Theorems.Thm_GlobalTheory_FreeQuotient_isFreeRingAction_iff_inertia_eq_bot

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
theorem _root_.solution :
    IsFreeRingAction G A ↔ ∀ P : Ideal A, P.IsPrime → P.inertia G = ⊥ := by
  refine ⟨fun h P hP ↦ ?_, fun h ↦
    (isFreeRingAction_iff_inertia_eq_bot G A).mpr fun P hP ↦ h P hP.isPrime⟩
  obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hP.ne_top
  rw [eq_bot_iff, ← (isFreeRingAction_iff_inertia_eq_bot G A).mp h Q hQ]
  exact fun g hg ↦ AddSubgroup.mem_inertia.mpr fun a ↦ hle (AddSubgroup.mem_inertia.mp hg a)
end GlobalTheory.FreeQuotient
