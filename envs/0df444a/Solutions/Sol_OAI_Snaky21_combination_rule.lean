-- Prove2me | solution 1 for OAI.Snaky21.combination_rule
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-08T07:40:08.425872+00:00
-- url     : https://prove2.me/submissions/2260d0d8-17e4-49fb-989c-f79c6eef8c7b

import Definitions.Def_Snaky21Core

namespace OAI.Snaky21
open SnakyPrototype

theorem hasSnaky_mono {M M' : Finset Cell} (h : M ⊆ M') :
    HasSnaky M → HasSnaky M' := by
  rintro ⟨r, t, ht⟩
  exact ⟨r, t, ht.trans h⟩

theorem freshCell_not_mem (M B : Finset Cell) : freshCell M B ∉ M ∪ B := by
  intro hm
  have hh := Finset.le_sup (f := fun x : Cell => x.1.natAbs) hm
  simp only [freshCell, Int.natAbs_natCast] at hh
  omega

theorem fresh_exists (M B : Finset Cell) : ∃ m : Cell, m ∉ M ∧ m ∉ B := by
  exact ⟨freshCell M B, by simpa only [Finset.mem_union, not_or] using freshCell_not_mem M B⟩

theorem won_canForce (n : ℕ) {M B : Finset Cell} (h : HasSnaky M) :
    CanForce n M B := by
  cases n with
  | zero => exact h
  | succ n =>
    obtain ⟨m, hm, hb⟩ := fresh_exists M B
    exact ⟨m, hm, hb, Or.inl (hasSnaky_mono (Finset.subset_insert _ _) h)⟩

theorem canForce_step {n : ℕ} {M B : Finset Cell} :
    CanForce n M B → CanForce (n + 1) M B := by
  induction n generalizing M B with
  | zero => exact won_canForce 1
  | succ n ih =>
    rintro ⟨m, hm, hb, hw⟩
    refine ⟨m, hm, hb, ?_⟩
    rcases hw with hw | hw
    · exact Or.inl hw
    · exact Or.inr (fun b hbm hbb => ih (hw b hbm hbb))

theorem canForce_mono {n m : ℕ} (hnm : n ≤ m) {M B : Finset Cell}
    (h : CanForce n M B) : CanForce m M B := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact canForce_step ih

theorem mem_unionRequired {x : Cell} {cs : List Card} :
    x ∈ unionRequired cs ↔ ∃ c ∈ cs, x ∈ c.required := by
  induction cs with
  | nil => simp [unionRequired]
  | cons c cs ih =>
    change x ∈ c.required ∪ unionRequired cs ↔ _
    simp only [Finset.mem_union, ih, List.mem_cons, exists_eq_or_imp]

theorem mem_unionEnvelope {x : Cell} {cs : List Card} :
    x ∈ unionEnvelope cs ↔ ∃ c ∈ cs, x ∈ c.envelope := by
  induction cs with
  | nil => simp [unionEnvelope]
  | cons c cs ih =>
    change x ∈ c.envelope ∪ unionEnvelope cs ↔ _
    simp only [Finset.mem_union, ih, List.mem_cons, exists_eq_or_imp]

theorem mem_commonEnvelope {x : Cell} {cs : List Card} (hne : cs ≠ []) :
    x ∈ commonEnvelope cs ↔ ∀ c ∈ cs, x ∈ c.envelope := by
  cases cs with
  | nil => contradiction
  | cons c cs =>
    simp only [commonEnvelope]
    have aux : ∀ ds : List Card,
        x ∈ ds.foldr (fun d s => d.envelope ∩ s) c.envelope ↔
          x ∈ c.envelope ∧ ∀ d ∈ ds, x ∈ d.envelope := by
      intro ds
      induction ds with
      | nil => simp
      | cons d ds ih => simp only [List.foldr_cons, Finset.mem_inter, ih,
          List.mem_cons, forall_eq_or_imp]; tauto
    rw [aux]
    simp

theorem height_le_max {c : Card} {cs : List Card} (hc : c ∈ cs) :
    c.height ≤ maxHeight cs := by
  induction cs with
  | nil => simp at hc
  | cons d cs ih =>
    simp only [List.mem_cons] at hc
    simp only [maxHeight, List.map_cons, List.foldr_cons]
    rcases hc with rfl | hc
    · exact le_max_left _ _
    · exact (ih hc).trans (le_max_right _ _)

theorem combination_rule (p : Cell) (cs : List Card) (hne : cs ≠ [])
    (hv : ∀ c ∈ cs, Valid c) : Valid (combine p cs) := by
  refine ⟨?_, by simp [combine], ?_⟩
  · intro x hx
    simp only [combine, Finset.mem_erase, Finset.mem_union] at hx
    simp only [combine, Finset.mem_insert]
    right
    apply mem_unionEnvelope.mpr
    rcases hx.2 with hx | hx
    · obtain ⟨c, hc, hx⟩ := mem_unionRequired.mp hx
      exact ⟨c, hc, (hv c hc).1 hx⟩
    · obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil cs hne
      exact ⟨c, hc, (mem_commonEnvelope hne).mp hx c hc⟩
  · intro M B hA hB
    have hpB : p ∉ B := by
      intro hp
      exact Finset.disjoint_left.mp hB hp (by simp [combine])
    obtain ⟨m, hmM, hmB, hpm⟩ : ∃ m, m ∉ M ∧ m ∉ B ∧
        p ∈ insert m M := by
      by_cases hp : p ∈ M
      · obtain ⟨m, hmM, hmB⟩ := fresh_exists M B
        exact ⟨m, hmM, hmB, Finset.mem_insert_of_mem hp⟩
      · exact ⟨p, hp, hpB, Finset.mem_insert_self _ _⟩
    have howned : unionRequired cs ∪ commonEnvelope cs ⊆ insert m M := by
      intro x hx
      by_cases hxp : x = p
      · simpa [hxp] using hpm
      · exact Finset.mem_insert_of_mem (hA (by simpa [combine] using And.intro hxp hx))
    change CanForce (1 + maxHeight cs) M B
    rw [Nat.add_comm 1]
    refine ⟨m, hmM, hmB, Or.inr ?_⟩
    intro b hbm hbb
    have hncommon : b ∉ commonEnvelope cs := by
      intro hb
      exact hbm (howned (Finset.mem_union_right _ hb))
    obtain ⟨c, hc, hbc⟩ : ∃ c ∈ cs, b ∉ c.envelope := by
      by_contra h
      push_neg at h
      exact hncommon ((mem_commonEnvelope hne).mpr h)
    apply canForce_mono (height_le_max hc)
    apply (hv c hc).2.2
    · intro x hx
      exact howned (Finset.mem_union_left _ (mem_unionRequired.mpr ⟨c, hc, hx⟩))
    · rw [Finset.disjoint_insert_left]
      refine ⟨hbc, ?_⟩
      exact hB.mono_right (by
        intro x hx
        exact Finset.mem_insert_of_mem (mem_unionEnvelope.mpr ⟨c, hc, hx⟩))

theorem base_valid (i : Fin 6) : Valid (baseCard i) := by
  refine ⟨Finset.erase_subset _ _, by simp [baseCard], ?_⟩
  intro M B hM hB
  have hp : basePoint i ∈ snaky := by
    fin_cases i <;> decide
  have hs {M' : Finset Cell} (h : snaky ⊆ M') : HasSnaky M' := by
    refine ⟨0, (0, 0), ?_⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    change x + (0 : Cell) ∈ M'
    simpa only [add_zero] using h hx
  by_cases hi : basePoint i ∈ M
  · apply won_canForce
    apply hs
    intro x hx
    by_cases hxi : x = basePoint i
    · simpa [hxi] using hi
    · exact hM (Finset.mem_erase.mpr ⟨hxi, hx⟩)
  · refine ⟨basePoint i, hi, ?_, Or.inl (hs ?_)⟩
    · intro hb
      exact Finset.disjoint_left.mp hB hb hp
    · intro x hx
      by_cases hxi : x = basePoint i
      · simpa [hxi] using Finset.mem_insert_self (basePoint i) M
      · exact Finset.mem_insert_of_mem (hM (Finset.mem_erase.mpr ⟨hxi, hx⟩))

end OAI.Snaky21

open OAI.Snaky21 OAI.SnakyPrototype

theorem solution (p : Cell) (cs : List Card) (hne : cs ≠ [])
    (hv : ∀ c ∈ cs, Valid c) : Valid (combine p cs) :=
  combination_rule p cs hne hv

#print axioms solution
