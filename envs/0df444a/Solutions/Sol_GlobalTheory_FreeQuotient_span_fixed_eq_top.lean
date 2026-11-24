-- Prove2me | solution 1 for GlobalTheory.FreeQuotient.span_fixed_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:31:11.089674+00:00
-- url     : https://prove2.me/submissions/b9de34b1-1473-450b-93bd-74c3e946518e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Theorems.Thm_GlobalTheory_FreeQuotient_exists_sum_sub_card_smul_mem

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
theorem _root_.solution [Module.Finite A M]
    (h : ∀ P : Ideal A, P.IsMaximal → (Nat.card (P.inertia G) : A) ∉ P)
    (hM : ∀ P : Ideal A, P.IsMaximal → ∀ g ∈ P.inertia G, ∀ m : M,
      g • m - m ∈ P • (⊤ : Submodule A M)) :
    Submodule.span A {m : M | ∀ g : G, g • m = m} = ⊤ := by
  set N := Submodule.span A {m : M | ∀ g : G, g • m = m} with hN
  have : N.colon Set.univ = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    have htop : (⊤ : Submodule A M) ≤ N ⊔ P • ⊤ := by
      intro m _
      obtain ⟨s, hs⟩ := exists_sum_sub_card_smul_mem (G := G) P m fun g hg ↦ hM P hP g hg m
      obtain ⟨u, p, hp, hup⟩ := hP.exists_inv (h P hP)
      have h1 : ∑ p ∈ s, p.1 • ∑ g : G, g • (p.2 • m) ∈ N :=
        Submodule.sum_mem _ fun p _ ↦ N.smul_mem _
          (Submodule.subset_span fun g ↦ smul_sum_smul _ g)
      have h2 : (Nat.card (P.inertia G) : A) • m ∈ N ⊔ P • ⊤ := by
        have := sub_mem (Submodule.mem_sup_left (T := P • ⊤) h1) (Submodule.mem_sup_right hs)
        simpa using this
      have := add_mem (Submodule.smul_mem _ u h2)
        (Submodule.mem_sup_right (Submodule.smul_mem_smul hp (Submodule.mem_top (x := m))))
      rwa [smul_smul, ← add_smul, hup, one_smul] at this
    obtain ⟨r, hr, hr'⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
      Module.Finite.fg_top le_rfl htop
    have : r ∈ P := hle (Submodule.mem_colon.mpr fun m _ ↦
      hr' (Submodule.smul_mem_pointwise_smul m r ⊤ trivial))
    exact hP.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using P.sub_mem this hr))
  rw [eq_top_iff]
  intro m _
  have h1 : (1 : A) ∈ N.colon Set.univ := by rw [this]; trivial
  simpa using Submodule.mem_colon.mp h1 m trivial
end GlobalTheory.FreeQuotient
