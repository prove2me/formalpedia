-- Prove2me | solution 1 for GlobalTheory.FreeQuotient.exists_finset_inertia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:46:58.673569+00:00
-- url     : https://prove2.me/submissions/fe9aa6e4-3dcc-4c75-a828-f410a84fa191

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
variable (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass G B A]
variable {G A}
namespace GlobalTheory.FreeQuotient
theorem _root_.solution [Finite G] (P : Ideal A) [hP : P.IsMaximal] :
    ∃ s : Finset (A × A), (∀ g ∉ P.inertia G, ∑ p ∈ s, p.1 * g • p.2 = 0) ∧
      ∀ h ∈ P.inertia G, ∑ p ∈ s, p.1 * h • p.2 - 1 ∈ P := by
  refine exists_finset_separating P (P.inertia G : Set G)
    (fun h hh ↦ AddSubgroup.mem_inertia.mp hh) fun g hg ↦ ?_
  by_contra hne
  refine hg (AddSubgroup.mem_inertia.mpr fun a ↦ ?_)
  have := hP.eq_of_le hne le_sup_left
  change g • a - a ∈ P
  rw [this]
  exact Ideal.mem_sup_right (Ideal.subset_span ⟨a, rfl⟩)
end GlobalTheory.FreeQuotient
