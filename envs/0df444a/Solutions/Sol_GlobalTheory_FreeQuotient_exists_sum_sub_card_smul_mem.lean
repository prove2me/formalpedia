-- Prove2me | solution 1 for GlobalTheory.FreeQuotient.exists_sum_sub_card_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:04:51.854923+00:00
-- url     : https://prove2.me/submissions/6a00f93c-2ddc-4e1c-b368-caad0e78cb18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Theorems.Thm_GlobalTheory_FreeQuotient_exists_finset_inertia

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
variable {G : Type*} [Group G] [Fintype G] {A : Type*} [CommRing A] [MulSemiringAction G A]
  {M : Type*} [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
namespace GlobalTheory.FreeQuotient
theorem _root_.solution (P : Ideal A) [P.IsMaximal] (m : M)
    (hm : ∀ g ∈ P.inertia G, g • m - m ∈ P • (⊤ : Submodule A M)) :
    ∃ s : Finset (A × A), ∑ p ∈ s, p.1 • ∑ g : G, g • (p.2 • m) -
      (Nat.card (P.inertia G) : A) • m ∈ P • (⊤ : Submodule A M) := by
  classical
  obtain ⟨s, hs, hs'⟩ := exists_finset_inertia (G := G) P
  refine ⟨s, ?_⟩
  rw [sum_smul_sum_smul, ← Finset.sum_subset (Finset.filter_subset (· ∈ P.inertia G) _)
    (fun g _ hg ↦ by rw [hs g (by simpa using hg), zero_smul])]
  have : (Nat.card (P.inertia G) : A) • m =
      ∑ _g ∈ Finset.univ.filter (· ∈ P.inertia G), m := by
    rw [Finset.sum_const, Nat.cast_smul_eq_nsmul, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [this, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun g hg ↦ ?_
  have hg' : g ∈ P.inertia G := by simpa using hg
  have := add_mem (Submodule.smul_mem_smul (hs' g hg') (Submodule.mem_top (x := g • m)))
    (hm g hg')
  convert this using 1
  rw [sub_smul, one_smul]
  abel
end GlobalTheory.FreeQuotient
