-- Prove2me | solution 1 for KneserColouring.count_isAlt_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:44:24.205798+00:00
-- url     : https://prove2.me/submissions/a90e61d3-5472-4f62-8b86-4c1014d619c9

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Theorems.Thm_KneserColouring_NoComp_mono
public import Theorems.Thm_KneserColouring_NoComp_abs_inj
public import Theorems.Thm_KneserColouring_isAlt_insert
public import Theorems.Thm_KneserColouring_isAlt_zero_one_false

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
namespace KneserColouring
theorem _root_.solution (S : Finset ℤ) (hS : NoComp S) (hne : S.Nonempty) :
    (S.filter (fun a => IsAlt 0 (S.erase a))).card % 2 = 1 ↔ (IsAlt 0 S ∨ IsAlt 1 S) := by
  induction S using Finset.induction_on_max_value (f := fun x : ℤ => |x|) with
  | empty => exact absurd hne (by simp)
  | insert z T hz hmax ih =>
    have hlt : ∀ b ∈ T, |b| < |z| := by
      intro b hb
      refine lt_of_le_of_ne (hmax b hb) ?_
      intro h
      have := hS.abs_inj (mem_insert_of_mem hb) (mem_insert_self z T) h
      exact hz (this ▸ hb)
    have hST : NoComp T := hS.mono (subset_insert z T)
    -- compute the filter
    have hfil : (insert z T).filter (fun a => IsAlt 0 ((insert z T).erase a)) =
        if IsAlt 0 T then insert z (T.filter (fun a => IsAlt 0 (insert z (T.erase a))))
        else T.filter (fun a => IsAlt 0 (insert z (T.erase a))) := by
      rw [filter_insert, erase_insert hz]
      have : T.filter (fun a => IsAlt 0 ((insert z T).erase a)) =
          T.filter (fun a => IsAlt 0 (insert z (T.erase a))) := by
        apply filter_congr
        intro a ha
        rw [erase_insert_of_ne (fun h => hz (by subst h; exact ha))]
      rw [this]
    have hfil2 : T.filter (fun a => IsAlt 0 (insert z (T.erase a))) =
        if (0 < z ↔ Even (T.card - 1)) then T.filter (fun a => IsAlt 0 (T.erase a)) else ∅ := by
      split_ifs with hE
      · apply filter_congr
        intro a ha
        rw [isAlt_insert (fun h => hz (mem_of_mem_erase h))
          (fun b hb => hlt b (mem_of_mem_erase hb)),
          card_erase_of_mem ha, Nat.add_zero]
        exact and_iff_left hE
      · rw [filter_eq_empty_iff]
        intro a ha
        rw [isAlt_insert (fun h => hz (mem_of_mem_erase h))
          (fun b hb => hlt b (mem_of_mem_erase hb)),
          card_erase_of_mem ha, Nat.add_zero]
        exact fun h => hE h.2
    rw [hfil, hfil2, isAlt_insert hz hlt, isAlt_insert hz hlt]
    rcases T.eq_empty_or_nonempty with hT | hT
    · subst hT
      simp [IsAlt]
      omega
    have ih' := ih hST hT
    have hcard : 1 ≤ T.card := card_pos.2 hT
    have hnot := fun h0 h1 => isAlt_zero_one_false hT h0 h1
    have hpar : Even (T.card - 1) ↔ ¬ Even T.card := by
      obtain ⟨m, hm⟩ : ∃ m, T.card = m + 1 := ⟨T.card - 1, by omega⟩
      rw [hm, Nat.add_sub_cancel, Nat.even_add_one, not_not]
    have hpar1 : Even (T.card + 1) ↔ ¬ Even T.card := Nat.even_add_one
    rw [Nat.add_zero]
    have key1 : ∀ p q : Prop, ¬(p ↔ ¬q) → (p ↔ q) := by intro p q; tauto
    have key2 : ∀ p q : Prop, (p ↔ q) → ¬(p ↔ ¬q) := by intro p q; tauto
    by_cases hE : (0 < z ↔ Even (T.card - 1))
    · rw [if_pos hE]
      have hz1 : (0 < z ↔ Even (T.card + 1)) := by rw [hpar1, ← hpar]; exact hE
      have hz0 : ¬ (0 < z ↔ Even T.card) := by rw [hpar1] at hz1; intro h; exact key2 _ _ h hz1
      split_ifs with hP
      · rw [card_insert_of_notMem (fun h => hz (mem_of_mem_filter z h))]
        have : ¬ IsAlt 1 T := fun h1 => hnot hP h1
        constructor
        · intro h
          exfalso
          have := ih'.2 (Or.inl hP)
          omega
        · rintro (h | h)
          · exact absurd h.2 hz0
          · exact absurd h.1 this
      · constructor
        · intro h; right; exact ⟨(ih'.1 h).resolve_left hP, hz1⟩
        · intro h
          exact ih'.2 (Or.inr (h.resolve_left (fun h' => hz0 h'.2)).1)
    · rw [if_neg hE]
      have hz0 : (0 < z ↔ Even T.card) := by rw [hpar] at hE; exact key1 _ _ hE
      have hz1 : ¬ (0 < z ↔ Even (T.card + 1)) := by rw [hpar1]; exact key2 _ _ hz0
      split_ifs with hP
      · simp only [card_insert_of_notMem (notMem_empty z), card_empty]
        constructor
        · intro _; left; exact ⟨hP, hz0⟩
        · intro _; trivial
      · simp only [card_empty]
        constructor
        · intro h; omega
        · rintro (h | h)
          · exact absurd h.1 hP
          · exact absurd h.2 hz1
end KneserColouring
