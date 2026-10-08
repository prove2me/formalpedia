-- Prove2me | solution 1 for OAI.Snaky21.claim_calculus
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-08T07:47:52.816753+00:00
-- url     : https://prove2.me/submissions/8acbfe38-4c8b-4d4f-928a-c769ee9969a6

import Definitions.Def_Snaky21Core
import Theorems.Thm_OAI_Snaky21_combination_rule
open OAI.Snaky21 OAI.SnakyPrototype

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

namespace OAI.Snaky21
open SnakyPrototype

theorem orient_add (r : Fin 8) (x y : Cell) :
    orient r (x + y) = orient r x + orient r y := by
  fin_cases r <;> ext <;> simp [orient] <;> ring

theorem orient_neg (r : Fin 8) (x : Cell) : orient r (-x) = -orient r x := by
  fin_cases r <;> ext <;> simp [orient]

theorem orient_closed (r s : Fin 8) :
    ∃ u : Fin 8, ∀ x : Cell, orient r (orient s x) = orient u x := by
  fin_cases r <;> fin_cases s
  · exact ⟨0, by intro x; ext <;> simp [orient]⟩
  · exact ⟨1, by intro x; ext <;> simp [orient]⟩
  · exact ⟨2, by intro x; ext <;> simp [orient]⟩
  · exact ⟨3, by intro x; ext <;> simp [orient]⟩
  · exact ⟨4, by intro x; ext <;> simp [orient]⟩
  · exact ⟨5, by intro x; ext <;> simp [orient]⟩
  · exact ⟨6, by intro x; ext <;> simp [orient]⟩
  · exact ⟨7, by intro x; ext <;> simp [orient]⟩
  · exact ⟨1, by intro x; ext <;> simp [orient]⟩
  · exact ⟨0, by intro x; ext <;> simp [orient]⟩
  · exact ⟨3, by intro x; ext <;> simp [orient]⟩
  · exact ⟨2, by intro x; ext <;> simp [orient]⟩
  · exact ⟨5, by intro x; ext <;> simp [orient]⟩
  · exact ⟨4, by intro x; ext <;> simp [orient]⟩
  · exact ⟨7, by intro x; ext <;> simp [orient]⟩
  · exact ⟨6, by intro x; ext <;> simp [orient]⟩
  · exact ⟨2, by intro x; ext <;> simp [orient]⟩
  · exact ⟨5, by intro x; ext <;> simp [orient]⟩
  · exact ⟨0, by intro x; ext <;> simp [orient]⟩
  · exact ⟨7, by intro x; ext <;> simp [orient]⟩
  · exact ⟨6, by intro x; ext <;> simp [orient]⟩
  · exact ⟨1, by intro x; ext <;> simp [orient]⟩
  · exact ⟨4, by intro x; ext <;> simp [orient]⟩
  · exact ⟨3, by intro x; ext <;> simp [orient]⟩
  · exact ⟨3, by intro x; ext <;> simp [orient]⟩
  · exact ⟨4, by intro x; ext <;> simp [orient]⟩
  · exact ⟨1, by intro x; ext <;> simp [orient]⟩
  · exact ⟨6, by intro x; ext <;> simp [orient]⟩
  · exact ⟨7, by intro x; ext <;> simp [orient]⟩
  · exact ⟨0, by intro x; ext <;> simp [orient]⟩
  · exact ⟨5, by intro x; ext <;> simp [orient]⟩
  · exact ⟨2, by intro x; ext <;> simp [orient]⟩
  · exact ⟨4, by intro x; ext <;> simp [orient]⟩
  · exact ⟨3, by intro x; ext <;> simp [orient]⟩
  · exact ⟨6, by intro x; ext <;> simp [orient]⟩
  · exact ⟨1, by intro x; ext <;> simp [orient]⟩
  · exact ⟨0, by intro x; ext <;> simp [orient]⟩
  · exact ⟨7, by intro x; ext <;> simp [orient]⟩
  · exact ⟨2, by intro x; ext <;> simp [orient]⟩
  · exact ⟨5, by intro x; ext <;> simp [orient]⟩
  · exact ⟨5, by intro x; ext <;> simp [orient]⟩
  · exact ⟨2, by intro x; ext <;> simp [orient]⟩
  · exact ⟨7, by intro x; ext <;> simp [orient]⟩
  · exact ⟨0, by intro x; ext <;> simp [orient]⟩
  · exact ⟨1, by intro x; ext <;> simp [orient]⟩
  · exact ⟨6, by intro x; ext <;> simp [orient]⟩
  · exact ⟨3, by intro x; ext <;> simp [orient]⟩
  · exact ⟨4, by intro x; ext <;> simp [orient]⟩
  · exact ⟨6, by intro x; ext <;> simp [orient]⟩
  · exact ⟨7, by intro x; ext <;> simp [orient]⟩
  · exact ⟨4, by intro x; ext <;> simp [orient]⟩
  · exact ⟨5, by intro x; ext <;> simp [orient]⟩
  · exact ⟨2, by intro x; ext <;> simp [orient]⟩
  · exact ⟨3, by intro x; ext <;> simp [orient]⟩
  · exact ⟨0, by intro x; ext <;> simp [orient]⟩
  · exact ⟨1, by intro x; ext <;> simp [orient]⟩
  · exact ⟨7, by intro x; ext <;> simp [orient]⟩
  · exact ⟨6, by intro x; ext <;> simp [orient]⟩
  · exact ⟨5, by intro x; ext <;> simp [orient]⟩
  · exact ⟨4, by intro x; ext <;> simp [orient]⟩
  · exact ⟨3, by intro x; ext <;> simp [orient]⟩
  · exact ⟨2, by intro x; ext <;> simp [orient]⟩
  · exact ⟨1, by intro x; ext <;> simp [orient]⟩
  · exact ⟨0, by intro x; ext <;> simp [orient]⟩

theorem orient_injective (r : Fin 8) : Function.Injective (orient r) := by
  intro x y h
  fin_cases r <;> simp only [orient, Prod.mk.injEq, neg_inj] at h <;>
    apply Prod.ext <;> tauto

theorem orient_surjective (r : Fin 8) : Function.Surjective (orient r) := by
  intro x
  fin_cases r
  · exact ⟨x, rfl⟩
  · exact ⟨(x.2, x.1), rfl⟩
  · exact ⟨(x.1, -x.2), by simp [orient]⟩
  · exact ⟨(x.2, -x.1), by simp [orient]⟩
  · exact ⟨(-x.1, x.2), by simp [orient]⟩
  · exact ⟨(-x.2, x.1), by simp [orient]⟩
  · exact ⟨(-x.1, -x.2), by simp [orient]⟩
  · exact ⟨(-x.2, -x.1), by simp [orient]⟩

theorem placement_injective (r : Fin 8) (t : Cell) :
    Function.Injective (placement r t) := by
  intro x y h
  apply orient_injective r
  exact add_right_cancel h

theorem placement_surjective (r : Fin 8) (t : Cell) :
    Function.Surjective (placement r t) := by
  intro y
  obtain ⟨x, hx⟩ := orient_surjective r (y - t)
  exact ⟨x, by simp [placement, hx]⟩

theorem mem_placement_image (r : Fin 8) (t : Cell) (x : Cell) (s : Finset Cell) :
    placement r t x ∈ s.image (placement r t) ↔ x ∈ s := by
  constructor
  · intro h
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp h
    have hxy := placement_injective r t he
    simpa only [hxy] using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

theorem hasSnaky_placed (r : Fin 8) (t : Cell) {M : Finset Cell}
    (h : HasSnaky M) : HasSnaky (M.image (placement r t)) := by
  obtain ⟨s, u, hu⟩ := h
  obtain ⟨v, hv⟩ := orient_closed r s
  refine ⟨v, orient r u + t, ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  have hh : placement r t (placement s u x) = placement v (orient r u + t) x := by
    simp only [placement, orient_add, hv]
    abel
  rw [← hh]
  exact Finset.mem_image.mpr ⟨placement s u x, hu (Finset.mem_image.mpr ⟨x, hx, rfl⟩), rfl⟩

theorem canForce_transport (n : ℕ) (r : Fin 8) (t : Cell)
    {M B : Finset Cell} (h : CanForce n M B) :
    CanForce n (M.image (placement r t)) (B.image (placement r t)) := by
  induction n generalizing M B with
  | zero => exact hasSnaky_placed r t h
  | succ n ih =>
    obtain ⟨m, hmM, hmB, hw⟩ := h
    have hinj := placement_injective r t
    refine ⟨placement r t m, ?_, ?_, ?_⟩
    · simpa only [mem_placement_image] using hmM
    · simpa only [mem_placement_image] using hmB
    rw [← Finset.image_insert]
    rcases hw with hw | hw
    · exact Or.inl (hasSnaky_placed r t hw)
    · refine Or.inr ?_
      intro b hbM hbB
      obtain ⟨b₀, rfl⟩ := placement_surjective r t b
      rw [← Finset.image_insert]
      apply ih
      apply hw
      · simpa only [mem_placement_image] using hbM
      · simpa only [mem_placement_image] using hbB

theorem placed_valid (r : Fin 8) (t : Cell) {c : Card} (h : Valid c) :
    Valid (placed r t c) := by
  refine ⟨Finset.image_subset_image h.1, h.2.1, ?_⟩
  intro M B hM hB
  let f := placement r t
  let M₀ := M.preimage f (placement_injective r t).injOn
  let B₀ := B.preimage f (placement_injective r t).injOn
  have hforce : CanForce c.height M₀ B₀ := by
    apply h.2.2
    · intro x hx
      apply Finset.mem_preimage.mpr
      exact hM (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    · apply Finset.disjoint_left.mpr
      intro x hxB hxT
      exact Finset.disjoint_left.mp hB (Finset.mem_preimage.mp hxB)
        (Finset.mem_image.mpr ⟨x, hxT, rfl⟩)
  have himg (s : Finset Cell) :
      (s.preimage f (placement_injective r t).injOn).image f = s := by
    apply Finset.ext
    intro y
    constructor
    · rintro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_preimage.mp hx
    · intro hy
      obtain ⟨x, rfl⟩ := placement_surjective r t y
      exact Finset.mem_image.mpr ⟨x, Finset.mem_preimage.mpr hy, rfl⟩
  have hh := canForce_transport c.height r t hforce
  change CanForce c.height (M₀.image f) (B₀.image f) at hh
  rw [show M₀.image f = M from himg M, show B₀.image f = B from himg B] at hh
  exact hh

end OAI.Snaky21

theorem solution : (∀ i : Fin 6, Valid (baseCard i)) ∧ (∀ (r : Fin 8) (t : Cell) (c : Card), Valid c → Valid (placed r t c)) ∧ (∀ (p : Cell) (cs : List Card), cs ≠ [] → (∀ c ∈ cs, Valid c) → Valid (combine p cs)) :=
  ⟨base_valid, fun r t c hc => placed_valid r t hc, combination_rule⟩
