-- Prove2me | solution 1 for GlobalTheory.card_le_absNorm_of_forall_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:24:47.881542+00:00
-- url     : https://prove2.me/submissions/fe99c961-2556-4748-9c62-30b149328686

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDivisorsLeAbsNormNumberField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (I : Ideal (𝓞 F)), I ≠ ⊥ →
    ∀ s : Finset (Ideal (𝓞 F)), (∀ J ∈ s, I ≤ J) → s.card ≤ Ideal.absNorm I := by
  intro F _ _ I hI s hs
  classical
  haveI : Finite (𝓞 F ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  letI : Fintype (𝓞 F ⧸ I) := Fintype.ofFinite _
  have hgen : ∀ J : Ideal (𝓞 F), ∃ a : 𝓞 F, I ≤ J → I ⊔ Ideal.span {a} = J := by
    intro J
    by_cases h : I ≤ J
    · obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq h hI
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose g hg using hgen
  have hle : ∀ J K : Ideal (𝓞 F), I ≤ J → I ≤ K →
      Ideal.Quotient.mk I (g J) = Ideal.Quotient.mk I (g K) → J ≤ K := by
    intro J K hJ hK heq
    rw [← hg J hJ]
    refine sup_le hK ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    have hd : g J - g K ∈ I := Ideal.Quotient.eq.mp heq
    have hk : g K ∈ K := by
      have h0 : g K ∈ I ⊔ Ideal.span {g K} := Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
      rwa [hg K hK] at h0
    have : g J = (g J - g K) + g K := by ring
    rw [this]
    exact K.add_mem (hK hd) hk
  have hinj : Set.InjOn (fun J => Ideal.Quotient.mk I (g J)) (s : Set (Ideal (𝓞 F))) := by
    intro J hJ K hK heq
    exact le_antisymm (hle J K (hs J hJ) (hs K hK) heq) (hle K J (hs K hK) (hs J hJ) heq.symm)
  have h1 : s.card ≤ (Finset.univ : Finset (𝓞 F ⧸ I)).card :=
    Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) hinj
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply] at h1
  exact h1
end GlobalTheory
