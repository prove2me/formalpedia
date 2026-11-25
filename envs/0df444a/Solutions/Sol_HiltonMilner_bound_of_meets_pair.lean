-- Prove2me | solution 1 for HiltonMilner.bound_of_meets_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:29:55.805644+00:00
-- url     : https://prove2.me/submissions/e5b5280d-c53a-44fc-b5a7-4dd7210f280b

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_CrossIntersecting
public import Definitions.Def_HiltonMilnerLib_HMCore
public import Theorems.Thm_HiltonMilner_cross_bound


set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner
namespace HiltonMilner
theorem _root_.solution {X : Finset ℕ} {n k y z : ℕ} (hX : #X = n) (hk : 2 ≤ k)
    (hn : 2 * k + 1 ≤ n) (hyX : y ∈ X) (hzX : z ∈ X) (hyz : y ≠ z) {𝒜 : Finset (Finset ℕ)}
    (h𝒜 : 𝒜 ⊆ powersetCard k X) (hc : Cross 𝒜 𝒜) (hnt : NonTriv X 𝒜)
    (hmeet : ∀ A ∈ 𝒜, y ∈ A ∨ z ∈ A) : #𝒜 ≤ hmNum n k := by
  set Y := (X.erase z).erase y with hYdef
  have hY : #Y = n - 2 := by
    rw [card_erase_of_mem (mem_erase.2 ⟨hyz, hyX⟩), card_erase_of_mem hzX, hX]; omega
  set 𝒜yz := 𝒜.filter (fun A => y ∈ A ∧ z ∈ A)
  set 𝒜y := 𝒜.filter (fun A => y ∈ A ∧ z ∉ A)
  set 𝒜z := 𝒜.filter (fun A => y ∉ A ∧ z ∈ A)
  have hsplit : #𝒜 = #𝒜yz + #𝒜y + #𝒜z := by
    have h1 := card_filter_add_card_filter_not (s := 𝒜) (fun A => y ∈ A)
    have h2 := card_filter_add_card_filter_not (s := 𝒜.filter (fun A => y ∈ A)) (fun A => z ∈ A)
    rw [filter_filter, filter_filter] at h2
    have h3 : 𝒜.filter (fun A => ¬ y ∈ A) = 𝒜z := by
      ext A; simp only [mem_filter, 𝒜z]
      constructor
      · rintro ⟨hA, hyA⟩; exact ⟨hA, hyA, (hmeet A hA).resolve_left hyA⟩
      · rintro ⟨hA, hyA, -⟩; exact ⟨hA, hyA⟩
    have e1 : 𝒜.filter (fun A => y ∈ A ∧ z ∈ A) = 𝒜yz := rfl
    have e2 : 𝒜.filter (fun A => y ∈ A ∧ ¬ z ∈ A) = 𝒜y := rfl
    rw [h3] at h1
    rw [e1, e2] at h2
    omega
  -- the members through both `y` and `z`
  have hyzb : #𝒜yz ≤ (n - 2).choose (k - 2) := by
    have hsub : 𝒜yz.image (fun A : Finset ℕ => (A.erase z).erase y) ⊆ powersetCard (k - 2) Y := by
      intro C hC
      obtain ⟨A, hA, rfl⟩ := mem_image.1 hC
      rw [mem_filter] at hA
      have hA' := mem_powersetCard.1 (h𝒜 hA.1)
      refine mem_powersetCard.2 ⟨erase_subset_erase _ (erase_subset_erase _ hA'.1), ?_⟩
      rw [card_erase_of_mem (mem_erase.2 ⟨hyz, hA.2.1⟩), card_erase_of_mem hA.2.2, hA'.2]
      omega
    have hinj : Set.InjOn (fun A : Finset ℕ => (A.erase z).erase y) 𝒜yz := by
      intro A hA B hB hAB
      simp only [coe_filter, Set.mem_ofPred_eq, 𝒜yz] at hA hB
      simp only at hAB
      have hA1 : y ∈ A.erase z := mem_erase.2 ⟨hyz, hA.2.1⟩
      have hB1 : y ∈ B.erase z := mem_erase.2 ⟨hyz, hB.2.1⟩
      rw [← insert_erase hA.2.2, ← insert_erase hB.2.2, ← insert_erase hA1, ← insert_erase hB1,
        hAB]
    have := card_le_card hsub
    rwa [card_image_of_injOn hinj, card_powersetCard, hY] at this
  -- the members through exactly one of them: cross-intersecting families on `Y`
  set ℬy := 𝒜y.image (fun A : Finset ℕ => A.erase y)
  set ℬz := 𝒜z.image (fun A : Finset ℕ => A.erase z)
  have hcy : #ℬy = #𝒜y := by
    refine card_image_of_injOn fun A hA B hB hAB => ?_
    simp only [coe_filter, Set.mem_ofPred_eq, 𝒜y] at hA hB
    rw [← insert_erase hA.2.1, ← insert_erase hB.2.1]
    exact congrArg (insert y) hAB
  have hcz : #ℬz = #𝒜z := by
    refine card_image_of_injOn fun A hA B hB hAB => ?_
    simp only [coe_filter, Set.mem_ofPred_eq, 𝒜z] at hA hB
    rw [← insert_erase hA.2.2, ← insert_erase hB.2.2]
    exact congrArg (insert z) hAB
  have hℬy : ℬy ⊆ powersetCard (k - 1) Y := by
    intro C hC
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hC
    rw [mem_filter] at hA
    have hA' := mem_powersetCard.1 (h𝒜 hA.1)
    refine mem_powersetCard.2 ⟨fun x hx => ?_, by rw [card_erase_of_mem hA.2.1, hA'.2]⟩
    rw [mem_erase] at hx
    refine mem_erase.2 ⟨hx.1, mem_erase.2 ⟨?_, hA'.1 hx.2⟩⟩
    rintro rfl; exact hA.2.2 hx.2
  have hℬz : ℬz ⊆ powersetCard (k - 1) Y := by
    intro C hC
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hC
    rw [mem_filter] at hA
    have hA' := mem_powersetCard.1 (h𝒜 hA.1)
    refine mem_powersetCard.2 ⟨fun x hx => ?_, by rw [card_erase_of_mem hA.2.2, hA'.2]⟩
    rw [mem_erase] at hx
    refine mem_erase.2 ⟨?_, mem_erase.2 ⟨hx.1, hA'.1 hx.2⟩⟩
    rintro rfl; exact hA.2.1 hx.2
  have hcross : Cross ℬy ℬz := by
    intro C hC D hD
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hC
    obtain ⟨B, hB, rfl⟩ := mem_image.1 hD
    rw [mem_filter] at hA hB
    obtain ⟨w, hw⟩ := hc A hA.1 B hB.1
    rw [mem_inter] at hw
    refine ⟨w, mem_inter.2 ⟨mem_erase.2 ⟨?_, hw.1⟩, mem_erase.2 ⟨?_, hw.2⟩⟩⟩
    · rintro rfl; exact hB.2.1 hw.2
    · rintro rfl; exact hA.2.2 hw.1
  have hyne : ℬy.Nonempty := by
    obtain ⟨A, hA, hzA⟩ := hnt z hzX
    exact ⟨_, mem_image.2 ⟨A, mem_filter.2 ⟨hA, (hmeet A hA).resolve_right hzA, hzA⟩, rfl⟩⟩
  have hzne : ℬz.Nonempty := by
    obtain ⟨A, hA, hyA⟩ := hnt y hyX
    exact ⟨_, mem_image.2 ⟨A, mem_filter.2 ⟨hA, hyA, (hmeet A hA).resolve_left hyA⟩, rfl⟩⟩
  have hCI := cross_bound (n - 2) Y hY (k - 1) (by omega) (by omega) ℬy ℬz hℬy hℬz hyne hzne
    hcross
  rw [show n - 2 - (k - 1) = n - k - 1 by omega] at hCI
  have hP : (n - 1).choose (k - 1) = (n - 2).choose (k - 2) + (n - 2).choose (k - 1) := by
    have := Nat.choose_succ_succ' (n - 2) (k - 2)
    rw [show n - 2 + 1 = n - 1 by omega, show k - 2 + 1 = k - 1 by omega] at this
    exact this
  have hm : (n - k - 1).choose (k - 1) ≤ (n - 2).choose (k - 1) :=
    Nat.choose_le_choose _ (by omega)
  unfold hmNum
  omega
end HiltonMilner
