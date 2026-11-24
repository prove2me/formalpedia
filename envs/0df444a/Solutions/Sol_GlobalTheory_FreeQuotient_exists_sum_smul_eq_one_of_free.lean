-- Prove2me | solution 1 for GlobalTheory.FreeQuotient.exists_sum_smul_eq_one_of_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:42:17.918772+00:00
-- url     : https://prove2.me/submissions/30830287-fe46-4c48-80ca-4637c9c08f50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Theorems.Thm_GlobalTheory_FreeQuotient_isFreeRingAction_iff_inertia_eq_bot
import Theorems.Thm_GlobalTheory_FreeQuotient_exists_sum_smul_eq_one

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
variable {G : Type*} [Group G] {A : Type*} [CommRing A] [MulSemiringAction G A]
namespace GlobalTheory.FreeQuotient
theorem _root_.solution [Fintype G] (h : IsFreeRingAction G A) :
    ∃ c : A, ∑ g : G, g • c = 1 :=
  exists_sum_smul_eq_one G A fun P hP ↦ by
    rw [(isFreeRingAction_iff_inertia_eq_bot G A).mp h P hP]
    simpa using (Ideal.ne_top_iff_one P).mp hP.ne_top
end GlobalTheory.FreeQuotient
