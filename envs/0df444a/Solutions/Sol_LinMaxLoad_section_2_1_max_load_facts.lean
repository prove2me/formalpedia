-- Prove2me | solution 1 for LinMaxLoad.section_2_1_max_load_facts
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:49:40.271054+00:00
-- url     : https://prove2.me/submissions/50fd7ee1-553f-40b5-9907-07febd3459a3

import Mathlib
import Definitions.Def_LinMaxLoad_maxLoad

section
set_option autoImplicit false
namespace LinMaxLoad.Dev.S21

theorem card_le_maxLoad {A B : Type*} [DecidableEq B] (h : A → B) (S : Finset A) (b : B) :
    (S.filter fun a => h a = b).card ≤ LinMaxLoad.maxLoad h S := by
  by_cases hb : b ∈ S.image h
  · exact Finset.le_sup (f := fun b => (S.filter fun a => h a = b).card) hb
  · have : (S.filter fun a => h a = b) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro a ha hab
      exact hb (Finset.mem_image.mpr ⟨a, ha, hab⟩)
    rw [this]; simp

end LinMaxLoad.Dev.S21
namespace LinMaxLoad
open LinMaxLoad.Dev.S21 in
theorem chk_section_2_1_max_load_facts {A B : Type*} [DecidableEq A] [DecidableEq B] (h : A → B)
    (S T : Finset A) :
    maxLoad h (S ∪ T) ≤ maxLoad h S + maxLoad h T ∧ (S ⊆ T → maxLoad h S ≤ maxLoad h T) := by
  constructor
  · unfold maxLoad
    apply Finset.sup_le
    intro b _
    calc ((S ∪ T).filter fun a => h a = b).card
        ≤ (S.filter fun a => h a = b).card + (T.filter fun a => h a = b).card := by
          rw [Finset.filter_union]; exact Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add (card_le_maxLoad h S b) (card_le_maxLoad h T b)
  · intro hST
    unfold maxLoad
    apply Finset.sup_le
    intro b hb
    calc (S.filter fun a => h a = b).card ≤ (T.filter fun a => h a = b).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ hST)
      _ ≤ _ := card_le_maxLoad h T b
end LinMaxLoad
end

theorem solution : type_of% @LinMaxLoad.chk_section_2_1_max_load_facts := @LinMaxLoad.chk_section_2_1_max_load_facts
