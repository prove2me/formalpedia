-- Prove2me | solution 1 for HiltonMilner.hm_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:32:33.06313+00:00
-- url     : https://prove2.me/submissions/49b4517a-b26d-4721-be24-1b275fbc2c49

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_CrossIntersecting
public import Definitions.Def_HiltonMilnerLib_HMCore
public import Theorems.Thm_HiltonMilner_nonempty_of_nonTriv
public import Theorems.Thm_HiltonMilner_meets_pair_of_sh_trivial
public import Theorems.Thm_HiltonMilner_bound_of_meets_pair
public import Theorems.Thm_HiltonMilner_Cross_mono
public import Theorems.Thm_HiltonMilner_card_low_add_high
public import Theorems.Thm_HiltonMilner_card_meeting
public import Theorems.Thm_HiltonMilner_card_sh
public import Theorems.Thm_HiltonMilner_card_union_lt_of_mem
public import Theorems.Thm_HiltonMilner_cross_bound
public import Theorems.Thm_HiltonMilner_cross_high_low
public import Theorems.Thm_HiltonMilner_fwt_sh_lt
public import Theorems.Thm_HiltonMilner_high_subset
public import Theorems.Thm_HiltonMilner_low_subset
public import Theorems.Thm_HiltonMilner_lt_max_of_mem_erase
public import Theorems.Thm_HiltonMilner_meet_erase_of_fixed
public import Theorems.Thm_HiltonMilner_mem_high
public import Theorems.Thm_HiltonMilner_sh_subset_powersetCard
public import Theorems.Thm_HiltonMilner_shift_mem_of_fixed


set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner
namespace HiltonMilner
theorem _root_.solution (n : ℕ) : ∀ (k : ℕ), 2 ≤ k → 2 * k ≤ n → ∀ (X : Finset ℕ), #X = n →
    ∀ 𝒜 : Finset (Finset ℕ), 𝒜 ⊆ powersetCard k X → Cross 𝒜 𝒜 → NonTriv X 𝒜 →
    #𝒜 ≤ hmNum n k := by
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro k hk hkn X hX 𝒜 h𝒜 hc hnt
  have hXne : X.Nonempty := by rw [← card_pos]; omega
  have h𝒜n := nonempty_of_nonTriv hXne hnt
  rcases Nat.eq_or_lt_of_le hkn with hn | hn
  · -- `n = 2k`: the cross-intersecting bound with `𝒜 = ℬ`
    have := cross_bound n X hX k (by omega) hkn 𝒜 𝒜 h𝒜 h𝒜 h𝒜n h𝒜n hc
    have hP : (2 * k).choose k = 2 * (2 * k - 1).choose (k - 1) := by
      have h3 := Nat.choose_succ_succ' (2 * k - 1) (k - 1)
      rw [show 2 * k - 1 + 1 = 2 * k by omega, show k - 1 + 1 = k by omega] at h3
      have h4 : (2 * k - 1).choose k = (2 * k - 1).choose (k - 1) := by
        rw [← Nat.choose_symm (show k - 1 ≤ 2 * k - 1 by omega)]
        congr 1; omega
      omega
    unfold hmNum
    rw [← hn, show 2 * k - k - 1 = k - 1 by omega, Nat.choose_self] at *
    rw [← hn] at this
    rw [show 2 * k - k = k by omega, Nat.choose_self] at this
    omega
  have hn1 : 2 * k + 1 ≤ n := hn
  set z := X.max' hXne with hz
  have hzX : z ∈ X := X.max'_mem hXne
  set Y := X.erase z with hYdef
  have hY : #Y = n - 1 := by rw [card_erase_of_mem hzX, hX]
  suffices key : ∀ W, ∀ 𝒜 : Finset (Finset ℕ), 𝒜 ⊆ powersetCard k X → Cross 𝒜 𝒜 →
      NonTriv X 𝒜 → fwt 𝒜 = W → #𝒜 ≤ hmNum n k from key _ 𝒜 h𝒜 hc hnt rfl
  intro W
  induction W using Nat.strong_induction_on with
  | _ W ihW =>
  intro 𝒜 h𝒜 hc hnt hW
  by_cases hmov : ∃ y ∈ Y, sh y z 𝒜 ≠ 𝒜
  · obtain ⟨y, hy, hne⟩ := hmov
    have hyz : y < z := lt_max_of_mem_erase hXne hy
    have hyX : y ∈ X := mem_of_mem_erase hy
    by_cases hnt' : NonTriv X (sh y z 𝒜)
    · have := ihW _ (hW ▸ fwt_sh_lt hyz hne) (sh y z 𝒜) (sh_subset_powersetCard hyX h𝒜) hc.sh
        hnt' rfl
      rwa [card_sh] at this
    · exact bound_of_meets_pair hX hk hn1 hyX hzX hyz.ne h𝒜 hc hnt
        (meets_pair_of_sh_trivial hnt hnt')
  push Not at hmov
  -- `𝒜` is fixed by every shift into `z`
  have hfix : ∀ y ∈ Y, sh y z 𝒜 = 𝒜 := hmov
  have hsplit := card_low_add_high z 𝒜
  -- the members avoiding `z`: a nontrivial intersecting family on `Y`
  have hlow : low z 𝒜 ⊆ powersetCard k Y := low_subset h𝒜
  have hlowc : Cross (low z 𝒜) (low z 𝒜) := hc.mono (filter_subset _ _) (filter_subset _ _)
  have hlownt : NonTriv Y (low z 𝒜) := by
    intro x hx
    have hxX : x ∈ X := mem_of_mem_erase hx
    have hxz : x ≠ z := ne_of_mem_erase hx
    obtain ⟨A, hA, hxA⟩ := hnt x hxX
    have hA' := mem_powersetCard.1 (h𝒜 hA)
    by_cases hzA : z ∈ A
    · obtain ⟨y, hyX, hyA⟩ := exists_mem_notMem_of_card_lt_card (s := insert x A) (t := X)
        (by have := card_insert_le x A; rw [hA'.2] at this; omega)
      have hyz : y ≠ z := fun e => hyA (mem_insert_of_mem (e ▸ hzA))
      have hyx : y ≠ x := fun e => hyA (e ▸ mem_insert_self _ _)
      have hyA' : y ∉ A := fun h => hyA (mem_insert_of_mem h)
      have hA2 := shift_mem_of_fixed (hfix y (mem_erase.2 ⟨hyz, hyX⟩)) hA hyA' hzA
      refine ⟨_, mem_filter.2 ⟨hA2, ?_⟩, ?_⟩
      · rw [mem_insert, mem_erase]
        rintro (h | ⟨h, -⟩)
        · exact hyz h.symm
        · exact h rfl
      · rw [mem_insert, mem_erase]
        rintro (h | ⟨-, h⟩)
        · exact hyx h.symm
        · exact hxA h
    · exact ⟨A, mem_filter.2 ⟨hA, hzA⟩, hxA⟩
  have hIH0 := ihn (n - 1) (by omega) k hk (by omega) Y hY (low z 𝒜) hlow hlowc hlownt
  unfold hmNum at hIH0
  rw [show n - 1 - 1 = n - 2 by omega, show n - 1 - k - 1 = n - k - 2 by omega] at hIH0
  -- the members through `z`: an intersecting family of `(k - 1)`-sets on `Y`
  have hhigh : high z 𝒜 ⊆ powersetCard (k - 1) Y := high_subset h𝒜
  have hhighc : Cross (high z 𝒜) (high z 𝒜) := by
    intro C hC D hD
    obtain ⟨A, hA, hzA, rfl⟩ := mem_high.1 hC
    obtain ⟨B, hB, hzB, rfl⟩ := mem_high.1 hD
    exact meet_erase_of_fixed hc hfix hA hB hzA hzB
      (card_union_lt_of_mem (mem_powersetCard.1 (h𝒜 hA)).2 (mem_powersetCard.1 (h𝒜 hB)).2
        hzA hzB (by omega))
  have hcross : Cross (high z 𝒜) (low z 𝒜) := cross_high_low hc
  -- binomial identities
  have hP1 : (n - 1).choose (k - 1) = (n - 2).choose (k - 1) + (n - 2).choose (k - 2) := by
    have := Nat.choose_succ_succ' (n - 2) (k - 2)
    rw [show n - 2 + 1 = n - 1 by omega, show k - 2 + 1 = k - 1 by omega] at this
    rw [this]; ring
  have hP2 : (n - k - 1).choose (k - 1) =
      (n - k - 2).choose (k - 1) + (n - k - 2).choose (k - 2) := by
    have := Nat.choose_succ_succ' (n - k - 2) (k - 2)
    rw [show n - k - 2 + 1 = n - k - 1 by omega, show k - 2 + 1 = k - 1 by omega] at this
    rw [this]; ring
  have hm1 : (n - k - 2).choose (k - 1) ≤ (n - 2).choose (k - 1) :=
    Nat.choose_le_choose _ (by omega)
  have hm2 : (n - k - 2).choose (k - 2) ≤ (n - 2).choose (k - 2) :=
    Nat.choose_le_choose _ (by omega)
  -- the bound for the high part
  have hhb : #(high z 𝒜) ≤ (n - 2).choose (k - 2) - (n - k - 2).choose (k - 2) := by
    by_cases hhnt : NonTriv Y (high z 𝒜)
    · -- nontrivial: induction (impossible for `k = 2`)
      rcases Nat.eq_or_lt_of_le hk with hk2 | hk3
      · exfalso
        have hYne : Y.Nonempty := by rw [← card_pos]; omega
        obtain ⟨C, hC⟩ := nonempty_of_nonTriv hYne hhnt
        have hC' := mem_powersetCard.1 (hhigh hC)
        rw [← hk2] at hC'
        obtain ⟨p, rfl⟩ := card_eq_one.1 hC'.2
        obtain ⟨D, hD, hpD⟩ := hhnt p (hC'.1 (mem_singleton_self p))
        obtain ⟨w, hw⟩ := hhighc _ hC D hD
        rw [mem_inter, mem_singleton] at hw
        exact hpD (hw.1 ▸ hw.2)
      · have := ihn (n - 1) (by omega) (k - 1) (by omega) (by omega) Y hY (high z 𝒜) hhigh
          hhighc hhnt
        unfold hmNum at this
        rw [show n - 1 - 1 = n - 2 by omega, show k - 1 - 1 = k - 2 by omega,
          show n - 1 - (k - 1) - 1 = n - k - 1 by omega] at this
        have hR : (n - k - 1).choose (k - 2) =
            (n - k - 2).choose (k - 2) + (n - k - 2).choose (k - 3) := by
          have := Nat.choose_succ_succ' (n - k - 2) (k - 3)
          rw [show n - k - 2 + 1 = n - k - 1 by omega, show k - 3 + 1 = k - 2 by omega] at this
          rw [this]; ring
        have hU : 0 < (n - k - 2).choose (k - 3) := Nat.choose_pos (by omega)
        have hm3 : (n - k - 1).choose (k - 2) ≤ (n - 2).choose (k - 2) :=
          Nat.choose_le_choose _ (by omega)
        omega
    · -- trivial: all members contain some `x`, and they meet a low member avoiding `x`
      unfold NonTriv at hhnt
      push Not at hhnt
      obtain ⟨x, hxY, hx⟩ := hhnt
      obtain ⟨B, hB, hxB⟩ := hlownt x hxY
      have hB' := mem_powersetCard.1 (hlow hB)
      set Y' := Y.erase x
      have hY' : #Y' = n - 2 := by rw [card_erase_of_mem hxY, hY]; omega
      have hBY' : B ⊆ Y' := fun w hw => mem_erase.2 ⟨fun e => hxB (e ▸ hw), hB'.1 hw⟩
      have hsub : (high z 𝒜).image (fun C : Finset ℕ => C.erase x) ⊆
          (powersetCard (k - 2) Y').filter (fun D => (D ∩ B).Nonempty) := by
        intro D hD
        obtain ⟨C, hC, rfl⟩ := mem_image.1 hD
        have hC' := mem_powersetCard.1 (hhigh hC)
        refine mem_filter.2 ⟨mem_powersetCard.2 ⟨erase_subset_erase _ hC'.1, ?_⟩, ?_⟩
        · rw [card_erase_of_mem (hx C hC), hC'.2]; omega
        · obtain ⟨w, hw⟩ := hcross C hC B hB
          rw [mem_inter] at hw
          exact ⟨w, mem_inter.2 ⟨mem_erase.2 ⟨fun e => hxB (e ▸ hw.2), hw.1⟩, hw.2⟩⟩
      have hinj : Set.InjOn (fun C : Finset ℕ => C.erase x) (high z 𝒜) := by
        intro C hC D hD hCD
        simp only at hCD
        rw [← insert_erase (hx C hC), ← insert_erase (hx D hD), hCD]
      have := card_le_card hsub
      rw [card_image_of_injOn hinj, card_meeting hBY', hY', hB'.2] at this
      rwa [show n - 2 - k = n - k - 2 by omega] at this
  unfold hmNum
  omega
end HiltonMilner
