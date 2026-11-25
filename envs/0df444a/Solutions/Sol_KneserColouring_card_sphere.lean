-- Prove2me | solution 1 for KneserColouring.card_sphere
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:55:25.296281+00:00
-- url     : https://prove2.me/submissions/71f9d3df-fef8-45cc-8e7f-0f989414a757

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Definitions.Def_KneserLib_TuckerRooms
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_TuckerMain
public import Theorems.Thm_KneserColouring_labSet_neg
public import Theorems.Thm_KneserColouring_isRoom_neg
public import Theorems.Thm_KneserColouring_labSet_zero_notMem
public import Theorems.Thm_KneserColouring_isAlt_image_neg
public import Theorems.Thm_KneserColouring_isAlt_zero_one_false


set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n : ℕ}
namespace KneserColouring
theorem _root_.solution (lab : (Fin n → SignType) → ℤ) (hanti : ∀ x, x ≠ 0 → lab (-x) = -lab x)
    (hNC : NoCompLab lab) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    (univ.filter (fun r : Room n => IsRoom k r ∧ IsAlt 0 (labSet lab k r) ∧
      (labSet lab k r).card = k)).card = altCount lab k := by
  set top : Fin n := ⟨k - 1, by omega⟩ with htop
  have hUp : ∀ r : Room n, IsUpper k r ↔ IsRoom k r ∧ r.1 top = 1 := by
    intro r
    unfold IsUpper
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2 top (by simp [htop]; omega)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun c hc => ?_⟩
      have : c = top := Fin.ext (by simp [htop]; omega)
      rw [this]
      exact h2
  rw [← card_filter_add_card_filter_not (fun r : Room n => r.1 top = 1)]
  have e1 : ((univ.filter (fun r : Room n => IsRoom k r ∧ IsAlt 0 (labSet lab k r) ∧
      (labSet lab k r).card = k)).filter (fun r => r.1 top = 1)).card =
      (univ.filter (fun r : Room n => IsUpper k r ∧ IsAlt 0 (labSet lab k r) ∧
      (labSet lab k r).card = k)).card := by
    congr 1
    ext r
    simp only [mem_filter, mem_univ, true_and, hUp]
    tauto
  have e2 : ((univ.filter (fun r : Room n => IsRoom k r ∧ IsAlt 0 (labSet lab k r) ∧
      (labSet lab k r).card = k)).filter (fun r => ¬ r.1 top = 1)).card =
      (univ.filter (fun r : Room n => IsUpper k r ∧ IsAlt 1 (labSet lab k r) ∧
      (labSet lab k r).card = k)).card := by
    apply card_nbij' (fun r => (-r.1, r.2)) (fun r => (-r.1, r.2))
    · rintro ⟨t, ρ⟩ hr
      simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hr ⊢
      obtain ⟨⟨hR, hA, hc⟩, ht⟩ := hr
      have hR' : IsRoom k (-t, ρ) := isRoom_neg.2 hR
      have hL := labSet_neg lab hanti hR' hkn
      rw [neg_neg] at hL
      refine ⟨(hUp _).2 ⟨hR', ?_⟩, ?_, ?_⟩
      · have hne : t top ≠ 0 := (hR.1 top).2 (by simp [htop]; omega)
        simp only [Pi.neg_apply]
        revert hne ht
        cases t top <;> decide
      · rw [hL] at hA
        exact (isAlt_image_neg (labSet_zero_notMem hNC hR' hkn)).1 hA
      · rw [hL, card_image_of_injective _ neg_injective] at hc
        exact hc
    · rintro ⟨t, ρ⟩ hr
      simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hr ⊢
      obtain ⟨hU, hA, hc⟩ := hr
      have hR := ((hUp _).1 hU).1
      have ht := ((hUp _).1 hU).2
      have hL := labSet_neg lab hanti hR hkn
      refine ⟨⟨isRoom_neg.2 hR, ?_, ?_⟩, ?_⟩
      · rw [hL]
        exact (isAlt_image_neg (labSet_zero_notMem hNC hR hkn)).2 hA
      · rw [hL, card_image_of_injective _ neg_injective]
        exact hc
      · simp only [Pi.neg_apply]
        simp only at ht
        rw [ht]
        decide
    · rintro ⟨t, ρ⟩ _
      simp
    · rintro ⟨t, ρ⟩ _
      simp
  have e3 : altCount lab k = (univ.filter (fun r : Room n => IsUpper k r ∧
      IsAlt 0 (labSet lab k r) ∧ (labSet lab k r).card = k)).card +
      (univ.filter (fun r : Room n => IsUpper k r ∧ IsAlt 1 (labSet lab k r) ∧
      (labSet lab k r).card = k)).card := by
    rw [altCount, ← card_union_of_disjoint]
    · congr 1
      ext r
      simp only [mem_filter, mem_union, mem_univ, true_and]
      tauto
    · rw [disjoint_filter]
      rintro r - ⟨-, h0, hc⟩ ⟨-, h1, -⟩
      exact isAlt_zero_one_false (by rw [← card_pos, hc]; omega) h0 h1
  rw [e1, e2, e3]
end KneserColouring
