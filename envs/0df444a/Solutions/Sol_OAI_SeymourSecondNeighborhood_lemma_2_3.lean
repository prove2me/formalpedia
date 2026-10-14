-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-13T20:36:41.023358+00:00
-- url     : https://prove2.me/submissions/9bfe1843-0659-40ba-a215-b239b243d623

import Mathlib
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_SeymourSecondNeighborhood_Image

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset

namespace OAI.SeymourSecondNeighborhood.Sol_OAI_SeymourSecondNeighborhood_lemma_2_3

/-! ### Generic facts about `fwd` -/

section fwd
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mem_fwd (r : V → V → Prop) (S : Finset V) (y : V) :
    y ∈ fwd r S ↔ ∃ x ∈ S, r x y := by
  unfold fwd
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem fwd_mono (r : V → V → Prop) {A B : Finset V} (h : A ⊆ B) : fwd r A ⊆ fwd r B := by
  intro y hy
  rw [mem_fwd] at hy ⊢
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨x, h hx, hxy⟩

theorem fwd_union_subset (r : V → V → Prop) (A B : Finset V) :
    fwd r (A ∪ B) ⊆ fwd r A ∪ fwd r B := by
  intro y hy
  rw [mem_fwd] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  rw [Finset.mem_union] at hx ⊢
  rcases hx with hx | hx
  · exact Or.inl ((mem_fwd r A y).2 ⟨x, hx, hxy⟩)
  · exact Or.inr ((mem_fwd r B y).2 ⟨x, hx, hxy⟩)

theorem fwd_univ_of_posIndeg (r : V → V → Prop) (hin : PosIndeg r) : fwd r univ = univ := by
  apply Finset.eq_univ_of_forall
  intro y
  rw [mem_fwd]
  obtain ⟨x, hx⟩ := hin y
  exact ⟨x, Finset.mem_univ _, hx⟩

end fwd

/-! ### The transitive tournament on `Fin m` -/

section tourn
variable {m : ℕ}

/-- The image operator of the transitive tournament on `Fin m`. -/
def f (A : Finset (Fin m)) : Finset (Fin m) := univ.filter (fun b => ∃ a ∈ A, a < b)

theorem mem_f (A : Finset (Fin m)) (b : Fin m) : b ∈ f A ↔ ∃ a ∈ A, a < b := by
  unfold f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem f_empty : f (∅ : Finset (Fin m)) = ∅ := by
  ext b
  rw [mem_f]
  simp

theorem f_f_subset (A : Finset (Fin m)) : f (f A) ⊆ f A := by
  intro b hb
  rw [mem_f] at hb ⊢
  obtain ⟨c, hc, hcb⟩ := hb
  rw [mem_f] at hc
  obtain ⟨a, ha, hac⟩ := hc
  exact ⟨a, ha, lt_trans hac hcb⟩

theorem min'_not_mem_f (B : Finset (Fin m)) (hB : B.Nonempty) : B.min' hB ∉ f B := by
  rw [mem_f]
  rintro ⟨a, ha, hlt⟩
  exact absurd (Finset.min'_le B a ha) (not_le.2 hlt)

theorem card_f_f_lt (A : Finset (Fin m)) (hA : (f A).Nonempty) : (f (f A)).card < (f A).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (f_f_subset A)]
  exact ⟨(f A).min' hA, Finset.min'_mem _ _, min'_not_mem_f (f A) hA⟩

theorem card_le_card_f_add_one (A : Finset (Fin m)) : A.card ≤ (f A).card + 1 := by
  rcases A.eq_empty_or_nonempty with h | h
  · subst h; simp
  · have hsub : A ⊆ insert (A.min' h) (f A) := by
      intro a ha
      rw [Finset.mem_insert]
      rcases eq_or_ne a (A.min' h) with heq | hne
      · exact Or.inl heq
      · right
        rw [mem_f]
        exact ⟨A.min' h, Finset.min'_mem _ _, lt_of_le_of_ne (Finset.min'_le A a ha) (Ne.symm hne)⟩
    exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)

theorem tourn_ineq (A : Finset (Fin m)) : A.card + (f (f A)).card ≤ 2 * (f A).card + 1 := by
  have h1 := card_le_card_f_add_one A
  rcases (f A).eq_empty_or_nonempty with h | h
  · rw [h] at h1
    rw [h, f_empty]
    simp only [Finset.card_empty] at h1 ⊢
    omega
  · have h2 := card_f_f_lt A h
    omega

theorem card_le_m (A : Finset (Fin m)) : A.card ≤ m := by
  have := Finset.card_le_univ A
  simpa [Fintype.card_fin] using this

end tourn

/-! ### Labels of a set of blown-up vertices in a block -/

section blocks
variable {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}

/-- The labels of `A` inside the block over `v`. -/
def lab (A : Finset (V × Fin m)) (v : V) : Finset (Fin m) := univ.filter (fun j => (v, j) ∈ A)

theorem mem_lab (A : Finset (V × Fin m)) (v : V) (j : Fin m) : j ∈ lab A v ↔ (v, j) ∈ A := by
  unfold lab
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The support (set of blocks met by `A`). -/
def supp (A : Finset (V × Fin m)) : Finset V := univ.filter (fun v => ∃ j, (v, j) ∈ A)

theorem mem_supp (A : Finset (V × Fin m)) (v : V) : v ∈ supp A ↔ ∃ j, (v, j) ∈ A := by
  unfold supp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem lab_eq_empty_of_not_mem_supp (A : Finset (V × Fin m)) (v : V) (hv : v ∉ supp A) :
    lab A v = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro j hj
  rw [mem_lab] at hj
  exact hv ((mem_supp A v).2 ⟨j, hj⟩)

theorem card_fiber (A : Finset (V × Fin m)) (v : V) :
    (A.filter (fun x => x.1 = v)).card = (lab A v).card := by
  have h : A.filter (fun x => x.1 = v) = (lab A v).image (fun j => (v, j)) := by
    ext ⟨w, j⟩
    simp only [Finset.mem_filter, Finset.mem_image, mem_lab, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, rfl⟩
      exact ⟨j, h1, rfl, rfl⟩
    · rintro ⟨i, hi, rfl, rfl⟩
      exact ⟨hi, rfl⟩
  rw [h, Finset.card_image_of_injective _ (Prod.mk_right_injective v)]

theorem card_eq_sum_lab (A : Finset (V × Fin m)) : A.card = ∑ v, (lab A v).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (fun _ _ => Finset.mem_univ _)]
  exact Finset.sum_congr rfl (fun v _ => card_fiber A v)

theorem card_lab_le (A : Finset (V × Fin m)) (v : V) : (lab A v).card ≤ m := card_le_m _

theorem supp_nonempty (U : Finset (V × Fin m)) (hU : U.Nonempty) : (supp U).Nonempty := by
  obtain ⟨⟨v, j⟩, h⟩ := hU
  exact ⟨v, (mem_supp U v).2 ⟨j, h⟩⟩

/-! ### The image operator of the blow-up -/

theorem mem_fwd_blowup (r : V → V → Prop) (U : Finset (V × Fin m)) (v : V) (j : Fin m) :
    (v, j) ∈ fwd (blowup r m) U ↔ v ∈ fwd r (supp U) ∨ j ∈ f (lab U v) := by
  rw [mem_fwd, mem_fwd, mem_f]
  constructor
  · rintro ⟨⟨w, i⟩, hx, h⟩
    unfold blowup at h
    simp only at h
    rcases h with h | ⟨rfl, hlt⟩
    · exact Or.inl ⟨w, (mem_supp U w).2 ⟨i, hx⟩, h⟩
    · exact Or.inr ⟨i, (mem_lab U w i).2 hx, hlt⟩
  · rintro (⟨w, hw, hwv⟩ | ⟨i, hi, hlt⟩)
    · obtain ⟨i, hi⟩ := (mem_supp U w).1 hw
      exact ⟨(w, i), hi, Or.inl hwv⟩
    · exact ⟨(v, i), (mem_lab U v i).1 hi, Or.inr ⟨rfl, hlt⟩⟩

theorem lab_fwd_blowup_of_mem (r : V → V → Prop) (U : Finset (V × Fin m)) (v : V)
    (hv : v ∈ fwd r (supp U)) : lab (fwd (blowup r m) U) v = univ := by
  apply Finset.eq_univ_of_forall
  intro j
  rw [mem_lab, mem_fwd_blowup]
  exact Or.inl hv

theorem lab_fwd_blowup_of_not_mem (r : V → V → Prop) (U : Finset (V × Fin m)) (v : V)
    (hv : v ∉ fwd r (supp U)) : lab (fwd (blowup r m) U) v = f (lab U v) := by
  ext j
  rw [mem_lab, mem_fwd_blowup]
  constructor
  · rintro (h | h)
    · exact absurd h hv
    · exact h
  · exact Or.inr

theorem supp_fwd_blowup_subset (r : V → V → Prop) (U : Finset (V × Fin m)) :
    supp (fwd (blowup r m) U) ⊆ supp U ∪ fwd r (supp U) := by
  intro v hv
  rw [mem_supp] at hv
  obtain ⟨j, hj⟩ := hv
  rw [mem_fwd_blowup] at hj
  rw [Finset.mem_union]
  rcases hj with h | h
  · exact Or.inr h
  · rw [mem_f] at h
    obtain ⟨i, hi, _⟩ := h
    rw [mem_lab] at hi
    exact Or.inl ((mem_supp U v).2 ⟨i, hi⟩)

/-- Sum of an indicator function. -/
theorem sum_indicator (X : Finset V) :
    (∑ v, (if v ∈ X then (1 : ℤ) else 0)) = X.card := by
  rw [Finset.sum_boole]
  congr 1
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]

end blocks


/-! ### Parts (a) and (b) -/

section ab
variable {V : Type*}

theorem isOriented_blowup (r : V → V → Prop) (hr : IsOriented r) (m : ℕ) :
    IsOriented (blowup r m) := by
  constructor
  · intro x h
    unfold blowup at h
    rcases h with h | ⟨_, h⟩
    · exact hr.loopless _ h
    · exact lt_irrefl _ h
  · intro x y hxy hyx
    unfold blowup at hxy hyx
    rcases hxy with h1 | ⟨e1, h1⟩ <;> rcases hyx with h2 | ⟨e2, h2⟩
    · exact hr.asymmetric h1 h2
    · rw [e2] at h1; exact hr.loopless _ h1
    · rw [e1] at h2; exact hr.loopless _ h2
    · exact lt_asymm h1 h2

theorem posIndeg_blowup (r : V → V → Prop) (hin : PosIndeg r) (m : ℕ) :
    PosIndeg (blowup r m) := by
  intro x
  obtain ⟨u, hu⟩ := hin x.1
  exact ⟨(u, x.2), Or.inl hu⟩

end ab

/-! ### Part (c): strict expansion -/

section c
variable {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}

/-- The pointwise (per-block) bound, valid for every block `v`. -/
theorem block_bound (r : V → V → Prop) (U : Finset (V × Fin m)) (v : V) :
    ((lab U v).card : ℤ) + (lab (fwd (blowup r m) (fwd (blowup r m) U)) v).card
      - 2 * (lab (fwd (blowup r m) U) v).card
    ≤ (m : ℤ) * ((if v ∈ supp U ∩ fwd r (supp U) then (1 : ℤ) else 0)
          - (if v ∈ fwd r (supp U) then (1 : ℤ) else 0))
      + (if v ∈ supp U \ fwd r (supp U) then (1 : ℤ) else 0)
      + (m : ℤ) * (if v ∈ fwd r (fwd r (supp U)) \ fwd r (supp U) then (1 : ℤ) else 0) := by
  have ha : (lab U v).card ≤ m := card_lab_le U v
  have hc : (lab (fwd (blowup r m) (fwd (blowup r m) U)) v).card ≤ m := card_lab_le _ v
  by_cases hv : v ∈ fwd r (supp U)
  · have hb : (lab (fwd (blowup r m) U) v).card = m := by
      rw [lab_fwd_blowup_of_mem r U v hv, Finset.card_univ, Fintype.card_fin]
    rw [hb]
    by_cases hs : v ∈ supp U
    · simp only [Finset.mem_inter, Finset.mem_sdiff, hs, hv, and_self, if_true, not_true_eq_false,
        and_false, if_false]
      omega
    · have ha0 : (lab U v).card = 0 := by
        rw [lab_eq_empty_of_not_mem_supp U v hs, Finset.card_empty]
      simp only [Finset.mem_inter, Finset.mem_sdiff, hs, hv, if_true, not_true_eq_false,
        and_false, false_and, if_false, ha0]
      omega
  · have hb : lab (fwd (blowup r m) U) v = f (lab U v) := lab_fwd_blowup_of_not_mem r U v hv
    rw [hb]
    have h1 := card_le_card_f_add_one (lab U v)
    by_cases hff : v ∈ fwd r (fwd r (supp U))
    · simp only [Finset.mem_inter, Finset.mem_sdiff, hv, hff, and_false, if_false,
        not_false_eq_true, and_true, if_true]
      by_cases hs : v ∈ supp U
      · simp only [hs, if_true]
        omega
      · have ha0 : (lab U v).card = 0 := by
          rw [lab_eq_empty_of_not_mem_supp U v hs, Finset.card_empty]
        simp only [hs, if_false, ha0]
        omega
    · have hvW : v ∉ fwd r (supp (fwd (blowup r m) U)) := by
        intro h
        have h2 := fwd_mono r (supp_fwd_blowup_subset r U) h
        have h3 := fwd_union_subset r _ _ h2
        rw [Finset.mem_union] at h3
        rcases h3 with h3 | h3
        · exact hv h3
        · exact hff h3
      rw [lab_fwd_blowup_of_not_mem r (fwd (blowup r m) U) v hvW, hb]
      have h2 := tourn_ineq (lab U v)
      simp only [Finset.mem_inter, Finset.mem_sdiff, hv, hff, and_false, if_false,
        not_false_eq_true, and_true]
      by_cases hs : v ∈ supp U
      · simp only [hs, if_true]
        omega
      · have ha0 : lab U v = ∅ := lab_eq_empty_of_not_mem_supp U v hs
        simp only [hs, if_false, ha0, f_empty, Finset.card_empty]
        omega

/-- Summing the right-hand side of `block_bound`. -/
theorem sum_bound (r : V → V → Prop) (U : Finset (V × Fin m)) :
    (∑ v, ((m : ℤ) * ((if v ∈ supp U ∩ fwd r (supp U) then (1 : ℤ) else 0)
          - (if v ∈ fwd r (supp U) then (1 : ℤ) else 0))
      + (if v ∈ supp U \ fwd r (supp U) then (1 : ℤ) else 0)
      + (m : ℤ) * (if v ∈ fwd r (fwd r (supp U)) \ fwd r (supp U) then (1 : ℤ) else 0)))
    = (m : ℤ) * (((supp U ∩ fwd r (supp U)).card : ℤ) - (fwd r (supp U)).card)
      + ((supp U \ fwd r (supp U)).card : ℤ)
      + (m : ℤ) * ((fwd r (fwd r (supp U)) \ fwd r (supp U)).card : ℤ) := by
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_indicator]

theorem strictExpander_blowup (r : V → V → Prop) (hin : PosIndeg r)
    (hdef : SubsetDeficit r) (hm : Fintype.card V < m) :
    StrictExpander (blowup r m) := by
  intro U hU hUne
  have hUc := card_eq_sum_lab U
  have hWc := card_eq_sum_lab (fwd (blowup r m) U)
  have hW2c := card_eq_sum_lab (fwd (blowup r m) (fwd (blowup r m) U))
  suffices h : (∑ v, (((lab U v).card : ℤ)
      + (lab (fwd (blowup r m) (fwd (blowup r m) U)) v).card
      - 2 * (lab (fwd (blowup r m) U) v).card)) < 0 by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at h
    have e1 : ((U.card : ℕ) : ℤ) = ∑ v, ((lab U v).card : ℤ) := by
      rw [hUc]; push_cast; rfl
    have e2 : (((fwd (blowup r m) U).card : ℕ) : ℤ)
        = ∑ v, ((lab (fwd (blowup r m) U) v).card : ℤ) := by
      rw [hWc]; push_cast; rfl
    have e3 : (((fwd (blowup r m) (fwd (blowup r m) U)).card : ℕ) : ℤ)
        = ∑ v, ((lab (fwd (blowup r m) (fwd (blowup r m) U)) v).card : ℤ) := by
      rw [hW2c]; push_cast; rfl
    rw [← e1, ← e2, ← e3] at h
    omega
  by_cases hS : supp U = univ
  · -- every block is reached in one step
    have hFS : fwd r (supp U) = univ := by
      rw [hS]; exact fwd_univ_of_posIndeg r hin
    have hpt : ∀ v, (((lab U v).card : ℤ)
        + (lab (fwd (blowup r m) (fwd (blowup r m) U)) v).card
        - 2 * (lab (fwd (blowup r m) U) v).card) ≤ ((lab U v).card : ℤ) - m := by
      intro v
      have hb : (lab (fwd (blowup r m) U) v).card = m := by
        rw [lab_fwd_blowup_of_mem r U v (by rw [hFS]; exact Finset.mem_univ v),
          Finset.card_univ, Fintype.card_fin]
      have hc := card_lab_le (fwd (blowup r m) (fwd (blowup r m) U)) v
      rw [hb]
      omega
    have hlt : U.card < Fintype.card V * m := by
      have := Finset.card_lt_card (Finset.ssubset_univ_iff.2 hUne)
      rwa [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at this
    have hlt' : (U.card : ℤ) < (Fintype.card V : ℤ) * m := by exact_mod_cast hlt
    calc _ ≤ ∑ v, (((lab U v).card : ℤ) - m) := Finset.sum_le_sum (fun v _ => hpt v)
      _ = (U.card : ℤ) - (Fintype.card V : ℤ) * m := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hUc]
        push_cast
        rw [nsmul_eq_mul]
      _ < 0 := by linarith
  · have hSne := supp_nonempty U hU
    have hd := hdef (supp U) hSne hS
    calc _ ≤ _ := Finset.sum_le_sum (fun v _ => block_bound r U v)
      _ = _ := sum_bound r U
      _ < 0 := by
        have h1 := Finset.card_sdiff_add_card_inter (fwd r (supp U)) (supp U)
        rw [Finset.inter_comm] at h1
        have h2 : (supp U \ fwd r (supp U)).card ≤ Fintype.card V := Finset.card_le_univ _
        have h3 : (m : ℤ) * (((fwd r (fwd r (supp U)) \ fwd r (supp U)).card : ℤ)
            - ((fwd r (supp U) \ supp U).card : ℤ)) ≤ (m : ℤ) * (-1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          omega
        have h1' : (((fwd r (supp U) \ supp U).card : ℕ) : ℤ)
            + ((supp U ∩ fwd r (supp U)).card : ℤ) = ((fwd r (supp U)).card : ℤ) := by
          exact_mod_cast h1
        have h2' : (((supp U \ fwd r (supp U)).card : ℕ) : ℤ) < m := by
          exact_mod_cast lt_of_le_of_lt h2 hm
        nlinarith [h1', h2', h3]

end c

end OAI.SeymourSecondNeighborhood.Sol_OAI_SeymourSecondNeighborhood_lemma_2_3

open OAI.SeymourSecondNeighborhood in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (r : V → V → Prop) (hr : IsOriented r)
    (hin : PosIndeg r) (hdef : SubsetDeficit r) (m : ℕ) (hm : Fintype.card V < m) :
    IsOriented (blowup r m) ∧ PosIndeg (blowup r m) ∧ StrictExpander (blowup r m) :=
  ⟨Sol_OAI_SeymourSecondNeighborhood_lemma_2_3.isOriented_blowup r hr m,
   Sol_OAI_SeymourSecondNeighborhood_lemma_2_3.posIndeg_blowup r hin m,
   Sol_OAI_SeymourSecondNeighborhood_lemma_2_3.strictExpander_blowup r hin hdef hm⟩
