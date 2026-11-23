-- Prove2me | solution 1 for GlobalTheory.FreeQuotient.isFreeRingAction_iff_inertia_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:24.430295+00:00
-- url     : https://prove2.me/submissions/ed5a79f3-bdbd-4f55-b5ed-96cc8e005397

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
theorem _root_.solution :
    IsFreeRingAction G A ↔ ∀ P : Ideal A, P.IsMaximal → P.inertia G = ⊥ := by
  constructor
  · intro h P hP
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    by_contra hg1
    refine hP.ne_top (top_le_iff.mp ?_)
    rw [← h g hg1, Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    exact AddSubgroup.mem_inertia.mp hg a
  · intro h g hg
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    have : g ∈ P.inertia G :=
      AddSubgroup.mem_inertia.mpr fun a ↦ hle (Ideal.subset_span ⟨a, rfl⟩)
    rw [h P hP] at this
    exact hg this
end GlobalTheory.FreeQuotient
