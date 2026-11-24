-- Prove2me | solution 1 for GlobalTheory.FinWeil.perfect_pairing_quotients
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:28:29.045791+00:00
-- url     : https://prove2.me/submissions/5e81b6b4-e449-45e7-8ce4-e791babd311d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PerfectPairingQuotients
import Theorems.Thm_GlobalTheory_FinWeil_exists_addChar_quotient
import Theorems.Thm_GlobalTheory_FinWeil_exists_injective_addChar
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_zero_left
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_zero_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil
namespace GlobalTheory.FinWeil
theorem _root_.solution : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (S A T₀ T : AddSubgroup X), (∀ a ∈ A, a ∈ S ↔ ∀ t ∈ T, γ a t = 1) → (∀ t ∈ T, t ∈ T₀ ↔ ∀ a ∈ A, γ a t = 1) → T₀.relIndex T ≠ 0 → S.relIndex A = T₀.relIndex T ∧ (∀ y : X, (∀ a ∈ A, a ∈ S → γ a y = 1) → ∃ t ∈ T, ∀ a ∈ A, γ a y = γ a t) ∧ ∀ t ∈ T, (∑ᶠ q : A ⧸ S.addSubgroupOf A, γ ((Quotient.out q : A) : X) t) = if t ∈ T₀ then (S.relIndex A : ℂ) else 0 := by
  intro R X M _ _ _ _ _ σ w γ W h S A T₀ T hS hT hfin
  have hS' : ∀ a : A, a ∈ S.addSubgroupOf A ↔ ∀ t : T, γ a t = 1 := by
    intro a
    rw [AddSubgroup.mem_addSubgroupOf, hS a a.2]
    simp
  have hT' : ∀ t : T, t ∈ T₀.addSubgroupOf T ↔ ∀ a : A, γ a t = 1 := by
    intro t
    rw [AddSubgroup.mem_addSubgroupOf, hT t t.2]
    simp
  obtain ⟨Φ, hΦi, hΦ⟩ := exists_injective_addChar (S.addSubgroupOf A) (T₀.addSubgroupOf T)
    (fun a t => γ a t) (fun x y z => h.add_left _ _ _) (fun x y z => h.add_right _ _ _)
    (fun x => h.zero_right _) (fun x => h.zero_left _) hS' (fun k hk => (hT' k).1 hk)
  obtain ⟨Ψ, hΨi, hΨ⟩ := exists_injective_addChar (T₀.addSubgroupOf T) (S.addSubgroupOf A)
    (fun t a => γ a t) (fun x y z => h.add_right _ _ _) (fun x y z => h.add_left _ _ _)
    (fun x => h.zero_left _) (fun x => h.zero_right _) hT' (fun k hk => (hS' k).1 hk)
  haveI : Finite (T ⧸ T₀.addSubgroupOf T) := Nat.finite_of_card_ne_zero hfin
  haveI : Finite (A ⧸ S.addSubgroupOf A) := Finite.of_injective Φ hΦi
  letI := Fintype.ofFinite (T ⧸ T₀.addSubgroupOf T)
  letI := Fintype.ofFinite (A ⧸ S.addSubgroupOf A)
  have c1 := Fintype.card_le_of_injective Φ hΦi
  have c2 := Fintype.card_le_of_injective Ψ hΨi
  have c3 := c2
  rw [AddChar.card_eq] at c1 c2
  have hc : Fintype.card (A ⧸ S.addSubgroupOf A) = Fintype.card (T ⧸ T₀.addSubgroupOf T) :=
    le_antisymm c1 c2
  have eA : S.relIndex A = Fintype.card (A ⧸ S.addSubgroupOf A) := Nat.card_eq_fintype_card
  have eT : T₀.relIndex T = Fintype.card (T ⧸ T₀.addSubgroupOf T) := Nat.card_eq_fintype_card
  refine ⟨by rw [eA, eT, hc], ?_, ?_⟩
  · intro y hy
    obtain ⟨χ, hχ⟩ := exists_addChar_quotient (S.addSubgroupOf A) (fun a : A => γ a y)
      (h.zero_left _) (fun a b => h.add_left _ _ _)
      (fun a ha => hy a a.2 (AddSubgroup.mem_addSubgroupOf.1 ha))
    have hb : Function.Bijective Ψ :=
      (Fintype.bijective_iff_injective_and_card Ψ).2 ⟨hΨi, by rw [AddChar.card_eq, hc]⟩
    obtain ⟨q, hq⟩ := hb.2 χ
    induction q using QuotientAddGroup.induction_on with | _ t
    refine ⟨t, t.2, fun a ha => ?_⟩
    have h1 := hΨ t ⟨a, ha⟩
    rw [hq, hχ] at h1
    exact h1
  · intro t ht
    rw [finsum_eq_sum_of_fintype]
    have h1 : ∀ q : A ⧸ S.addSubgroupOf A,
        γ ((Quotient.out q : A) : X) t = Ψ ((⟨t, ht⟩ : T) : T ⧸ T₀.addSubgroupOf T) q := by
      intro q
      conv_rhs => rw [← QuotientAddGroup.out_eq' q]
      rw [hΨ]
    rw [Finset.sum_congr rfl fun q _ => h1 q, AddChar.sum_eq_ite, eA]
    refine if_congr ?_ rfl rfl
    rw [hT t ht]
    constructor
    · intro h0 a ha
      have h2 := hΨ ⟨t, ht⟩ ⟨a, ha⟩
      rw [h0] at h2
      simpa using h2.symm
    · intro h0
      ext q
      rw [← h1, h0 _ (Quotient.out q).2]
      simp
end GlobalTheory.FinWeil
