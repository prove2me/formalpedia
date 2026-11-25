-- Prove2me | solution 1 for HiltonMilner.cross_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:24:43.737173+00:00
-- url     : https://prove2.me/submissions/292013b1-5a38-4650-a313-6e7dbf0f63fa

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
public import Definitions.Def_HiltonMilnerLib_CrossIntersecting
public import Theorems.Thm_HiltonMilner_card_meeting
public import Theorems.Thm_HiltonMilner_card_low_add_high
public import Theorems.Thm_HiltonMilner_mem_high
public import Theorems.Thm_HiltonMilner_low_subset
public import Theorems.Thm_HiltonMilner_high_subset
public import Theorems.Thm_HiltonMilner_cross_high_low
public import Theorems.Thm_HiltonMilner_card_union_lt_of_mem
public import Theorems.Thm_HiltonMilner_lt_max_of_mem_erase
public import Theorems.Thm_HiltonMilner_fwt_sh_le
public import Theorems.Thm_HiltonMilner_sh_nonempty
public import Theorems.Thm_HiltonMilner_cross_bound_base
public import Theorems.Thm_HiltonMilner_Cross_mono
public import Theorems.Thm_HiltonMilner_card_sh
public import Theorems.Thm_HiltonMilner_fwt_sh_lt
public import Theorems.Thm_HiltonMilner_meet_erase_of_fixed
public import Theorems.Thm_HiltonMilner_sh_subset_powersetCard
public import Theorems.Thm_HiltonMilner_shift_mem_of_fixed


set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner
namespace HiltonMilner
theorem _root_.solution (m : ℕ) : ∀ (X : Finset ℕ), #X = m → ∀ a, 1 ≤ a → 2 * a ≤ m →
    ∀ 𝒜 ℬ : Finset (Finset ℕ), 𝒜 ⊆ powersetCard a X → ℬ ⊆ powersetCard a X →
    𝒜.Nonempty → ℬ.Nonempty → Cross 𝒜 ℬ →
    #𝒜 + #ℬ ≤ m.choose a - (m - a).choose a + 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro X hX a ha1 ham
  rcases Nat.eq_or_lt_of_le ham with hm | hm
  · -- base case
    intro 𝒜 ℬ h𝒜 hℬ _ _ hc
    have := cross_bound_base (hX.trans hm.symm) h𝒜 hℬ hc
    rw [← hm, show 2 * a - a = a by omega, Nat.choose_self]
    omega
  have hXne : X.Nonempty := by rw [← card_pos]; omega
  set z := X.max' hXne with hz
  have hzX : z ∈ X := X.max'_mem hXne
  have hY : #(X.erase z) = m - 1 := by rw [card_erase_of_mem hzX, hX]
  suffices key : ∀ W, ∀ 𝒜 ℬ : Finset (Finset ℕ), 𝒜 ⊆ powersetCard a X → ℬ ⊆ powersetCard a X →
      𝒜.Nonempty → ℬ.Nonempty → Cross 𝒜 ℬ → fwt 𝒜 + fwt ℬ = W →
      #𝒜 + #ℬ ≤ m.choose a - (m - a).choose a + 1 from
    fun 𝒜 ℬ h𝒜 hℬ h𝒜n hℬn hc => key _ 𝒜 ℬ h𝒜 hℬ h𝒜n hℬn hc rfl
  intro W
  induction W using Nat.strong_induction_on with
  | _ W ihW =>
  intro 𝒜 ℬ h𝒜 hℬ h𝒜n hℬn hc hW
  by_cases hmov : ∃ y ∈ X.erase z, sh y z 𝒜 ≠ 𝒜 ∨ sh y z ℬ ≠ ℬ
  · obtain ⟨y, hy, hne⟩ := hmov
    have hyz : y < z := lt_max_of_mem_erase hXne hy
    have hyX : y ∈ X := mem_of_mem_erase hy
    have hlt : fwt (sh y z 𝒜) + fwt (sh y z ℬ) < W := by
      rw [← hW]
      rcases hne with hne | hne
      · have := fwt_sh_lt hyz hne; have := fwt_sh_le hyz ℬ; omega
      · have := fwt_sh_lt hyz hne; have := fwt_sh_le hyz 𝒜; omega
    have := ihW _ hlt (sh y z 𝒜) (sh y z ℬ) (sh_subset_powersetCard hyX h𝒜)
      (sh_subset_powersetCard hyX hℬ) (sh_nonempty h𝒜n) (sh_nonempty hℬn) hc.sh rfl
    rwa [card_sh, card_sh] at this
  push Not at hmov
  have hfix𝒜 : ∀ y ∈ X.erase z, sh y z 𝒜 = 𝒜 := fun y hy => (hmov y hy).1
  have hfixℬ : ∀ y ∈ X.erase z, sh y z ℬ = ℬ := fun y hy => (hmov y hy).2
  -- the low parts are nonempty
  have low_ne : ∀ 𝒞 : Finset (Finset ℕ), 𝒞 ⊆ powersetCard a X → 𝒞.Nonempty →
      (∀ y ∈ X.erase z, sh y z 𝒞 = 𝒞) → (low z 𝒞).Nonempty := by
    intro 𝒞 h𝒞 h𝒞n hfix
    obtain ⟨A, hA⟩ := h𝒞n
    have hA' := mem_powersetCard.1 (h𝒞 hA)
    by_cases hzA : z ∈ A
    · obtain ⟨y, hyX, hyA⟩ := exists_mem_notMem_of_card_lt_card (s := A) (t := X)
        (by rw [hA'.2, hX]; omega)
      have hyz : y ≠ z := fun e => hyA (e ▸ hzA)
      have hA2 := shift_mem_of_fixed (hfix y (mem_erase.2 ⟨hyz, hyX⟩)) hA hyA hzA
      refine ⟨_, mem_filter.2 ⟨hA2, ?_⟩⟩
      rw [mem_insert, mem_erase]
      rintro (h | ⟨h, -⟩)
      · exact hyz h.symm
      · exact h rfl
    · exact ⟨A, mem_filter.2 ⟨hA, hzA⟩⟩
  have h𝒜0 := low_ne 𝒜 h𝒜 h𝒜n hfix𝒜
  have hℬ0 := low_ne ℬ hℬ hℬn hfixℬ
  have hIH0 := ihm (m - 1) (by omega) (X.erase z) hY a ha1 (by omega) (low z 𝒜) (low z ℬ)
    (low_subset h𝒜) (low_subset hℬ) h𝒜0 hℬ0 (hc.mono (filter_subset _ _) (filter_subset _ _))
  have hsplit𝒜 := card_low_add_high z 𝒜
  have hsplitℬ := card_low_add_high z ℬ
  have hc10 : Cross (high z 𝒜) (low z ℬ) := cross_high_low hc
  have hc01 : Cross (high z ℬ) (low z 𝒜) := cross_high_low hc.symm
  -- binomial identities
  have hP : m.choose a = (m - 1).choose a + (m - 1).choose (a - 1) := by
    have := Nat.choose_succ_succ' (m - 1) (a - 1)
    rw [show m - 1 + 1 = m by omega, show a - 1 + 1 = a by omega] at this
    rw [this]; ring
  have hQ : (m - a).choose a = (m - 1 - a).choose a + (m - 1 - a).choose (a - 1) := by
    have := Nat.choose_succ_succ' (m - 1 - a) (a - 1)
    rw [show m - 1 - a + 1 = m - a by omega, show a - 1 + 1 = a by omega] at this
    rw [this]; ring
  have hm1 : (m - 1 - a).choose a ≤ (m - 1).choose a := Nat.choose_le_choose _ (by omega)
  have hm2 : (m - 1 - a).choose (a - 1) ≤ (m - 1).choose (a - 1) :=
    Nat.choose_le_choose _ (by omega)
  -- a bound for a high part when the other high part is empty
  have high_bound : ∀ 𝒞 𝒟 : Finset (Finset ℕ), 𝒞 ⊆ powersetCard a X → (low z 𝒟).Nonempty →
      Cross (high z 𝒞) (low z 𝒟) → 𝒟 ⊆ powersetCard a X →
      #(high z 𝒞) ≤ (m - 1).choose (a - 1) - (m - 1 - a).choose (a - 1) := by
    intro 𝒞 𝒟 h𝒞 hD0 hcr h𝒟
    obtain ⟨B, hB⟩ := hD0
    have hB' := mem_powersetCard.1 (low_subset h𝒟 hB)
    have hsub : high z 𝒞 ⊆ (powersetCard (a - 1) (X.erase z)).filter
        (fun D => (D ∩ B).Nonempty) :=
      fun C hC => mem_filter.2 ⟨high_subset h𝒞 hC, hcr C hC B hB⟩
    have := card_le_card hsub
    rwa [card_meeting hB'.1, hY, hB'.2] at this
  by_cases hA1 : (high z 𝒜).Nonempty
  · by_cases hB1 : (high z ℬ).Nonempty
    · -- both high parts are nonempty: they are cross-intersecting
      have hc11 : Cross (high z 𝒜) (high z ℬ) := by
        intro C hC D hD
        obtain ⟨A, hA, hzA, rfl⟩ := mem_high.1 hC
        obtain ⟨B, hB, hzB, rfl⟩ := mem_high.1 hD
        exact meet_erase_of_fixed hc hfixℬ hA hB hzA hzB
          (card_union_lt_of_mem (mem_powersetCard.1 (h𝒜 hA)).2 (mem_powersetCard.1 (hℬ hB)).2
            hzA hzB (by omega))
      rcases Nat.eq_or_lt_of_le ha1 with ha | ha
      · exfalso
        obtain ⟨C, hC⟩ := hA1
        obtain ⟨D, hD⟩ := hB1
        have hC0 := (mem_powersetCard.1 (high_subset h𝒜 hC)).2
        rw [← ha, Nat.sub_self, card_eq_zero] at hC0
        obtain ⟨w, hw⟩ := hc11 C hC D hD
        rw [hC0] at hw; simp at hw
      · have hIH1 := ihm (m - 1) (by omega) (X.erase z) hY (a - 1) (by omega) (by omega)
          (high z 𝒜) (high z ℬ) (high_subset h𝒜) (high_subset hℬ) hA1 hB1 hc11
        rw [show m - 1 - (a - 1) = m - a by omega] at hIH1
        have hR : (m - a).choose (a - 1) =
            (m - 1 - a).choose (a - 1) + (m - 1 - a).choose (a - 2) := by
          have := Nat.choose_succ_succ' (m - 1 - a) (a - 2)
          rw [show m - 1 - a + 1 = m - a by omega, show a - 2 + 1 = a - 1 by omega] at this
          rw [this]; ring
        have hU : 0 < (m - 1 - a).choose (a - 2) := Nat.choose_pos (by omega)
        have hm3 : (m - a).choose (a - 1) ≤ (m - 1).choose (a - 1) :=
          Nat.choose_le_choose _ (by omega)
        omega
    · rw [not_nonempty_iff_eq_empty] at hB1
      rw [hB1, card_empty] at hsplitℬ
      have := high_bound 𝒜 ℬ h𝒜 hℬ0 hc10 hℬ
      omega
  · rw [not_nonempty_iff_eq_empty] at hA1
    rw [hA1, card_empty] at hsplit𝒜
    have := high_bound ℬ 𝒜 hℬ h𝒜0 hc01 h𝒜
    omega
end HiltonMilner
