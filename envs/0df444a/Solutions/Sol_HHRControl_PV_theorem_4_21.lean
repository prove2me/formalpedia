-- Prove2me | solution 1 for HHRControl.PV.theorem_4_21
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:15:27.530204+00:00
-- url     : https://prove2.me/submissions/dce2fc51-12a9-4283-944c-2760e707e89a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages
import Theorems.Thm_HHRControl_PV_example_4_11
import Theorems.Thm_HHRControl_PV_approval_te_dc_criterion_mem_P
import Theorems.Thm_HHRControl_PV_approval_te_dc_certifier
import Theorems.Thm_HHRControl_PV_approval_tp_dc_criterion_mem_P
import Theorems.Thm_HHRControl_PV_approval_tp_dc_certifier

namespace HHRControl.PV

open Finset

/-! ## Generic facts about "argmax" winner sets -/

theorem filter_max_eq_singleton {α : Type*} [DecidableEq α] (D : Finset α) (f : α → ℕ) (c : α) :
    D.filter (fun x => ∀ y ∈ D, f y ≤ f x) = {c} ↔ c ∈ D ∧ ∀ y ∈ D, y ≠ c → f y < f c := by
  constructor
  · intro h
    have hc : c ∈ D.filter (fun x => ∀ y ∈ D, f y ≤ f x) := h ▸ mem_singleton_self c
    rw [mem_filter] at hc
    refine ⟨hc.1, fun y hy hyc => ?_⟩
    have hy' : y ∉ D.filter (fun x => ∀ y ∈ D, f y ≤ f x) := by
      rw [h, mem_singleton]; exact hyc
    rw [mem_filter] at hy'
    push Not at hy'
    obtain ⟨z, hz, hlt⟩ := hy' hy
    exact lt_of_lt_of_le hlt (hc.2 z hz)
  · rintro ⟨hc, h⟩
    ext x
    rw [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hx, hmax⟩
      by_contra hxc
      have := h x hx hxc
      have := hmax c hc
      omega
    · rintro rfl
      refine ⟨hc, fun y hy => ?_⟩
      by_cases hyx : y = x
      · rw [hyx]
      · exact (h y hy hyx).le

theorem mem_unique_max_iff {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℕ) (c : α) :
    c ∈ (if (univ.filter fun x => ∀ y ∈ (univ : Finset α), f y ≤ f x).card = 1 then
        (univ.filter fun x => ∀ y ∈ (univ : Finset α), f y ≤ f x) else ∅) ↔
      ∀ y, y ≠ c → f y < f c := by
  constructor
  · intro h
    split_ifs at h with hc
    · obtain ⟨w, hw⟩ := card_eq_one.1 hc
      have hcw : c = w := by rw [hw, mem_singleton] at h; exact h
      have h1 := (filter_max_eq_singleton univ f w).1 (by convert hw)
      intro y hy
      rw [hcw] at hy ⊢
      exact h1.2 y (mem_univ _) hy
    · simp at h
  · intro h
    have hW : (univ.filter fun x => ∀ y ∈ (univ : Finset α), f y ≤ f x) = {c} := by
      convert (filter_max_eq_singleton univ f c).2 ⟨mem_univ _, fun y _ hy => h y hy⟩
    rw [hW]
    simp

theorem unique_max_cases {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℕ) :
    (if (univ.filter fun x => ∀ y ∈ (univ : Finset α), f y ≤ f x).card = 1 then
        (univ.filter fun x => ∀ y ∈ (univ : Finset α), f y ≤ f x) else ∅) = ∅ ∨
      ∃ w, (if (univ.filter fun x => ∀ y ∈ (univ : Finset α), f y ≤ f x).card = 1 then
        (univ.filter fun x => ∀ y ∈ (univ : Finset α), f y ≤ f x) else ∅) = {w} := by
  split_ifs with hc
  · exact Or.inr (card_eq_one.1 hc)
  · exact Or.inl rfl

theorem split_count {n : ℕ} (p : Fin n → Prop) [DecidablePred p] (V₁ : Finset (Fin n)) :
    (V₁.filter p).card + (V₁ᶜ.filter p).card = (univ.filter p).card := by
  rw [← card_union_of_disjoint (disjoint_filter_filter disjoint_compl_right)]
  congr 1
  ext v
  simp only [mem_union, mem_filter, mem_compl, mem_univ, true_and]
  tauto

/-! ## Approval voting -/

section Approval

variable {m n : ℕ} (P : Fin n → Approval m)

theorem approval_diff (U : Finset (Fin n)) (x y : Fin m) :
    approvalScore P U x + (U.filter fun v => y ∈ P v ∧ x ∉ P v).card =
      approvalScore P U y + (U.filter fun v => x ∈ P v ∧ y ∉ P v).card := by
  have e1 : U.filter (fun v => x ∈ P v ∨ y ∈ P v) =
      U.filter (fun v => x ∈ P v) ∪ U.filter (fun v => y ∈ P v ∧ x ∉ P v) := by
    ext v; simp only [mem_filter, mem_union]; tauto
  have e2 : U.filter (fun v => x ∈ P v ∨ y ∈ P v) =
      U.filter (fun v => y ∈ P v) ∪ U.filter (fun v => x ∈ P v ∧ y ∉ P v) := by
    ext v; simp only [mem_filter, mem_union]; tauto
  have d1 : Disjoint (U.filter (fun v => x ∈ P v)) (U.filter (fun v => y ∈ P v ∧ x ∉ P v)) :=
    disjoint_filter.2 (fun v _ h1 h2 => h2.2 h1)
  have d2 : Disjoint (U.filter (fun v => y ∈ P v)) (U.filter (fun v => x ∈ P v ∧ y ∉ P v)) :=
    disjoint_filter.2 (fun v _ h1 h2 => h2.2 h1)
  unfold approvalScore
  rw [← card_union_of_disjoint d1, ← card_union_of_disjoint d2, ← e1, ← e2]

theorem mem_nominees_TE_approval (U : Finset (Fin n)) (c : Fin m) :
    c ∈ nominees .TE approval P U ↔
      ∀ y, y ≠ c → approvalScore P U y < approvalScore P U c := by
  simp only [nominees]
  have hw : approval.winners m n P univ U =
      univ.filter fun x => ∀ y ∈ (univ : Finset (Fin m)), approvalScore P U y ≤ approvalScore P U x := by
    ext x; simp [approval]
  rw [hw]
  convert mem_unique_max_iff (fun x => approvalScore P U x) c

theorem mem_nominees_TP_approval (U : Finset (Fin n)) (c : Fin m) :
    c ∈ nominees .TP approval P U ↔ ∀ y, approvalScore P U y ≤ approvalScore P U c := by
  simp [nominees, approval]

theorem twoStage_approval_eq_singleton (rule : TieRule) (V₁ : Finset (Fin n)) (c : Fin m) :
    twoStage rule approval P V₁ = {c} ↔
      c ∈ nominees rule approval P V₁ ∪ nominees rule approval P V₁ᶜ ∧
        ∀ y ∈ nominees rule approval P V₁ ∪ nominees rule approval P V₁ᶜ, y ≠ c →
          approvalScore P univ y < approvalScore P univ c := by
  unfold twoStage
  convert filter_max_eq_singleton (nominees rule approval P V₁ ∪ nominees rule approval P V₁ᶜ)
    (fun x => approvalScore P univ x) c using 2
  ext x; simp [approval]

/-- Destructive control by partition of voters, approval voting, model TE. -/
theorem dcpv_approval_TE_iff (c : Fin m) :
    DCPV .TE approval P c ↔ ∃ y z : Fin m, y ≠ c ∧ z ≠ c ∧
      (univ.filter fun v => c ∈ P v ∧ y ∉ P v ∧ z ∉ P v).card ≤
        (univ.filter fun v => c ∉ P v ∧ (y ∈ P v ∨ z ∈ P v)).card := by
  constructor
  · rintro ⟨V₁, hV₁⟩
    by_contra H
    push Not at H
    apply hV₁
    rw [twoStage_approval_eq_singleton]
    have uw : ∀ y, y ≠ c → approvalScore P univ y < approvalScore P univ c := by
      intro y hy
      have h1 := H y y hy hy
      have hd := approval_diff P univ c y
      have e1 : (univ.filter fun v => c ∉ P v ∧ (y ∈ P v ∨ y ∈ P v)) =
          univ.filter fun v => y ∈ P v ∧ c ∉ P v := by
        ext v; simp only [mem_filter, mem_univ, true_and]; tauto
      have e2 : (univ.filter fun v => c ∈ P v ∧ y ∉ P v ∧ y ∉ P v) =
          univ.filter fun v => c ∈ P v ∧ y ∉ P v := by
        ext v; simp only [mem_filter, mem_univ, true_and]; tauto
      rw [e1, e2] at h1
      omega
    refine ⟨?_, fun y _ hy => uw y hy⟩
    by_contra hn
    rw [mem_union, not_or, mem_nominees_TE_approval, mem_nominees_TE_approval] at hn
    push Not at hn
    obtain ⟨⟨y, hy, k1⟩, ⟨z, hz, k2⟩⟩ := hn
    have hH := H y z hy hz
    have hd1 := approval_diff P V₁ c y
    have hd2 := approval_diff P V₁ᶜ c z
    have s1 : (univ.filter fun v => c ∈ P v ∧ y ∉ P v ∧ z ∉ P v) ⊆
        (V₁.filter fun v => c ∈ P v ∧ y ∉ P v) ∪ (V₁ᶜ.filter fun v => c ∈ P v ∧ z ∉ P v) := by
      intro v hv
      simp only [mem_filter, mem_univ, true_and, mem_union, mem_compl] at hv ⊢
      tauto
    have s2 : (V₁.filter fun v => y ∈ P v ∧ c ∉ P v) ∪ (V₁ᶜ.filter fun v => z ∈ P v ∧ c ∉ P v) ⊆
        (univ.filter fun v => c ∉ P v ∧ (y ∈ P v ∨ z ∈ P v)) := by
      intro v hv
      simp only [mem_filter, mem_univ, true_and, mem_union, mem_compl] at hv ⊢
      tauto
    have dj : Disjoint (V₁.filter fun v => y ∈ P v ∧ c ∉ P v)
        (V₁ᶜ.filter fun v => z ∈ P v ∧ c ∉ P v) :=
      disjoint_filter_filter disjoint_compl_right
    have c1 := card_le_card s1
    have c2 := card_le_card s2
    rw [card_union_of_disjoint dj] at c2
    have c3 := card_union_le (V₁.filter fun v => c ∈ P v ∧ y ∉ P v)
      (V₁ᶜ.filter fun v => c ∈ P v ∧ z ∉ P v)
    omega
  · rintro ⟨y, z, hy, hz, hcard⟩
    set A := univ.filter fun v => y ∈ P v ∧ c ∉ P v with hA
    set B := univ.filter fun v => c ∈ P v ∧ y ∉ P v ∧ z ∉ P v with hB
    obtain ⟨Y, hYB, hYc⟩ :=
      exists_subset_card_eq (show min B.card A.card ≤ B.card from min_le_left _ _)
    have hY : ∀ v ∈ Y, c ∈ P v ∧ y ∉ P v ∧ z ∉ P v := fun v hv => by
      have := hYB hv; rw [hB, mem_filter] at this; exact this.2
    refine ⟨(univ.filter fun v => y ∈ P v) ∪ Y, fun hEq => ?_⟩
    rw [twoStage_approval_eq_singleton] at hEq
    obtain ⟨hcD, -⟩ := hEq
    rcases mem_union.1 hcD with h | h <;> rw [mem_nominees_TE_approval] at h
    · have k := h y hy
      have hd := approval_diff P ((univ.filter fun v => y ∈ P v) ∪ Y) c y
      have e1 : (((univ.filter fun v => y ∈ P v) ∪ Y).filter fun v => c ∈ P v ∧ y ∉ P v) ⊆ Y := by
        intro v hv
        simp only [mem_filter, mem_union, mem_univ, true_and] at hv
        tauto
      have e2 : A ⊆ (((univ.filter fun v => y ∈ P v) ∪ Y).filter fun v => y ∈ P v ∧ c ∉ P v) := by
        intro v hv
        rw [hA, mem_filter] at hv
        simp only [mem_filter, mem_union, mem_univ, true_and]
        tauto
      have := card_le_card e1
      have := card_le_card e2
      have := min_le_right B.card A.card
      omega
    · have k := h z hz
      have hd := approval_diff P ((univ.filter fun v => y ∈ P v) ∪ Y)ᶜ c z
      have e3 : (((univ.filter fun v => y ∈ P v) ∪ Y)ᶜ.filter fun v => c ∈ P v ∧ z ∉ P v) ⊆
          B \ Y := by
        intro v hv
        simp only [mem_filter, mem_union, mem_univ, true_and, mem_compl, not_or] at hv
        rw [mem_sdiff, hB, mem_filter]
        exact ⟨⟨mem_univ _, hv.2.1, hv.1.1, hv.2.2⟩, hv.1.2⟩
      have e4 : (univ.filter fun v => z ∈ P v ∧ c ∉ P v ∧ y ∉ P v) ⊆
          (((univ.filter fun v => y ∈ P v) ∪ Y)ᶜ.filter fun v => z ∈ P v ∧ c ∉ P v) := by
        intro v hv
        simp only [mem_filter, mem_union, mem_univ, true_and, mem_compl, not_or] at hv ⊢
        refine ⟨⟨hv.2.2, fun hvY => hv.2.1 (hY v hvY).1⟩, hv.1, hv.2.1⟩
      have e5 : (univ.filter fun v => c ∉ P v ∧ (y ∈ P v ∨ z ∈ P v)) ⊆
          A ∪ (univ.filter fun v => z ∈ P v ∧ c ∉ P v ∧ y ∉ P v) := by
        intro v hv
        rw [hA]
        simp only [mem_filter, mem_union, mem_univ, true_and] at hv ⊢
        tauto
      have := card_le_card e3
      have := card_le_card e4
      have := card_le_card e5
      have := card_union_le A (univ.filter fun v => z ∈ P v ∧ c ∉ P v ∧ y ∉ P v)
      have := card_sdiff_add_card_eq_card hYB
      omega

set_option maxHeartbeats 2000000 in
/-- Destructive control by partition of voters, approval voting, model TP. -/
theorem dcpv_approval_TP_iff (c : Fin m) :
    DCPV .TP approval P c ↔
      (∃ x : Fin m, x ≠ c ∧ approvalScore P univ c ≤ approvalScore P univ x) ∨
      ∃ y z : Fin m, y ≠ c ∧ z ≠ c ∧
        (univ.filter fun v => c ∈ P v ∧ y ∉ P v ∧ z ∉ P v).card + 2 ≤
          (univ.filter fun v => c ∉ P v ∧ (y ∈ P v ∨ z ∈ P v)).card ∧
        1 ≤ (univ.filter fun v => c ∉ P v ∧ y ∈ P v).card ∧
        1 ≤ (univ.filter fun v => c ∉ P v ∧ z ∈ P v).card := by
  constructor
  · rintro ⟨V₁, hV₁⟩
    by_contra H
    push Not at H
    obtain ⟨H1, H2⟩ := H
    apply hV₁
    rw [twoStage_approval_eq_singleton]
    refine ⟨?_, fun y _ hy => H1 y hy⟩
    by_contra hn
    rw [mem_union, not_or, mem_nominees_TP_approval, mem_nominees_TP_approval] at hn
    push Not at hn
    obtain ⟨⟨y, k1⟩, ⟨z, k2⟩⟩ := hn
    have hy : y ≠ c := by rintro rfl; omega
    have hz : z ≠ c := by rintro rfl; omega
    have hd1 := approval_diff P V₁ c y
    have hd2 := approval_diff P V₁ᶜ c z
    have s1 : (univ.filter fun v => c ∈ P v ∧ y ∉ P v ∧ z ∉ P v) ⊆
        (V₁.filter fun v => c ∈ P v ∧ y ∉ P v) ∪ (V₁ᶜ.filter fun v => c ∈ P v ∧ z ∉ P v) := by
      intro v hv
      simp only [mem_filter, mem_univ, true_and, mem_union, mem_compl] at hv ⊢
      tauto
    have s2 : (V₁.filter fun v => y ∈ P v ∧ c ∉ P v) ∪ (V₁ᶜ.filter fun v => z ∈ P v ∧ c ∉ P v) ⊆
        (univ.filter fun v => c ∉ P v ∧ (y ∈ P v ∨ z ∈ P v)) := by
      intro v hv
      simp only [mem_filter, mem_univ, true_and, mem_union, mem_compl] at hv ⊢
      tauto
    have t1 : (V₁.filter fun v => y ∈ P v ∧ c ∉ P v) ⊆
        (univ.filter fun v => c ∉ P v ∧ y ∈ P v) := by
      intro v hv
      simp only [mem_filter, mem_univ, true_and] at hv ⊢
      tauto
    have t2 : (V₁ᶜ.filter fun v => z ∈ P v ∧ c ∉ P v) ⊆
        (univ.filter fun v => c ∉ P v ∧ z ∈ P v) := by
      intro v hv
      simp only [mem_filter, mem_univ, true_and] at hv ⊢
      tauto
    have dj : Disjoint (V₁.filter fun v => y ∈ P v ∧ c ∉ P v)
        (V₁ᶜ.filter fun v => z ∈ P v ∧ c ∉ P v) :=
      disjoint_filter_filter disjoint_compl_right
    have c1 := card_le_card s1
    have c2 := card_le_card s2
    rw [card_union_of_disjoint dj] at c2
    have c3 := card_union_le (V₁.filter fun v => c ∈ P v ∧ y ∉ P v)
      (V₁ᶜ.filter fun v => c ∈ P v ∧ z ∉ P v)
    have c4 := card_le_card t1
    have c5 := card_le_card t2
    have := H2 y z hy hz (by omega) (by omega)
    omega
  · rintro (⟨x, hx, hle⟩ | ⟨y, z, hy, hz, h1, h2, h3⟩)
    · refine ⟨∅, fun hEq => ?_⟩
      rw [twoStage_approval_eq_singleton] at hEq
      obtain ⟨_, hall⟩ := hEq
      have hxD : x ∈ nominees .TP approval P ∅ ∪ nominees .TP approval P (∅ : Finset (Fin n))ᶜ := by
        apply mem_union_left
        rw [mem_nominees_TP_approval]
        intro y
        simp [approvalScore]
      have := hall x hxD hx
      omega
    · set P1 := univ.filter fun v => c ∉ P v ∧ y ∈ P v ∧ z ∉ P v with hP1
      set P2 := univ.filter fun v => c ∉ P v ∧ y ∉ P v ∧ z ∈ P v with hP2
      set P12 := univ.filter fun v => c ∉ P v ∧ y ∈ P v ∧ z ∈ P v with hP12
      set B := univ.filter fun v => c ∈ P v ∧ y ∉ P v ∧ z ∉ P v with hB
      set N2 := univ.filter fun v => c ∈ P v ∧ y ∈ P v ∧ z ∉ P v with hN2
      have f1 : (univ.filter fun v => c ∉ P v ∧ (y ∈ P v ∨ z ∈ P v)) ⊆ P1 ∪ P2 ∪ P12 := by
        intro v hv
        simp only [hP1, hP2, hP12, mem_filter, mem_univ, true_and, mem_union] at hv ⊢
        tauto
      have f2 : (univ.filter fun v => c ∉ P v ∧ y ∈ P v) ⊆ P1 ∪ P12 := by
        intro v hv
        simp only [hP1, hP12, mem_filter, mem_univ, true_and, mem_union] at hv ⊢
        tauto
      have f3 : (univ.filter fun v => c ∉ P v ∧ z ∈ P v) ⊆ P2 ∪ P12 := by
        intro v hv
        simp only [hP2, hP12, mem_filter, mem_univ, true_and, mem_union] at hv ⊢
        tauto
      have g1 := card_le_card f1
      have g2 := card_le_card f2
      have g3 := card_le_card f3
      have g4 := card_union_le (P1 ∪ P2) P12
      have g5 := card_union_le P1 P2
      have g6 := card_union_le P1 P12
      have g7 := card_union_le P2 P12
      obtain ⟨X, hXP, hXc⟩ : ∃ X ⊆ P12, X.card = if P1.card = 0 then 1 else 0 := by
        apply exists_subset_card_eq
        split_ifs with h0 <;> omega
      have hX : ∀ v ∈ X, c ∉ P v ∧ y ∈ P v ∧ z ∈ P v := fun v hv => by
        have := hXP hv; rw [hP12, mem_filter] at this; exact this.2
      obtain ⟨Y, hYB, hYc⟩ :=
        exists_subset_card_eq (show min B.card (P1.card + X.card - 1) ≤ B.card from
          min_le_left _ _)
      have hY : ∀ v ∈ Y, c ∈ P v ∧ y ∉ P v ∧ z ∉ P v := fun v hv => by
        have := hYB hv; rw [hB, mem_filter] at this; exact this.2
      have hXc' : (P1.card = 0 ∧ X.card = 1) ∨ (P1.card ≠ 0 ∧ X.card = 0) := by
        split_ifs at hXc with h0
        · exact Or.inl ⟨h0, hXc⟩
        · exact Or.inr ⟨h0, hXc⟩
      refine ⟨P1 ∪ N2 ∪ X ∪ Y, fun hEq => ?_⟩
      rw [twoStage_approval_eq_singleton] at hEq
      obtain ⟨hcD, -⟩ := hEq
      rcases mem_union.1 hcD with h | h <;> rw [mem_nominees_TP_approval] at h
      · have k := h y
        have hd := approval_diff P (P1 ∪ N2 ∪ X ∪ Y) c y
        have e1 : ((P1 ∪ N2 ∪ X ∪ Y).filter fun v => c ∈ P v ∧ y ∉ P v) ⊆ Y := by
          intro v hv
          simp only [hP1, hN2, mem_filter, mem_union, mem_univ, true_and] at hv
          have := hX v
          tauto
        have e2 : P1 ∪ X ⊆ ((P1 ∪ N2 ∪ X ∪ Y).filter fun v => y ∈ P v ∧ c ∉ P v) := by
          intro v hv
          have := hX v
          simp only [hP1, hN2, mem_filter, mem_union, mem_univ, true_and] at hv ⊢
          tauto
        have dj : Disjoint P1 X := by
          rw [disjoint_left]
          intro v h1 h2
          rw [hP1, mem_filter] at h1
          exact h1.2.2.2 (hX v h2).2.2
        have := card_le_card e1
        have := card_le_card e2
        rw [card_union_of_disjoint dj] at this
        have := min_le_right B.card (P1.card + X.card - 1)
        omega
      · have k := h z
        have hd := approval_diff P (P1 ∪ N2 ∪ X ∪ Y)ᶜ c z
        have e3 : ((P1 ∪ N2 ∪ X ∪ Y)ᶜ.filter fun v => c ∈ P v ∧ z ∉ P v) ⊆ B \ Y := by
          intro v hv
          simp only [hP1, hN2, mem_filter, mem_union, mem_univ, true_and, mem_compl,
            not_or] at hv
          rw [mem_sdiff, hB, mem_filter]
          refine ⟨⟨mem_univ _, hv.2.1, fun hyv => hv.1.1.1.2 ⟨hv.2.1, hyv, hv.2.2⟩, hv.2.2⟩,
            hv.1.2⟩
        have e4 : P2 ∪ (P12 \ X) ⊆ ((P1 ∪ N2 ∪ X ∪ Y)ᶜ.filter fun v => z ∈ P v ∧ c ∉ P v) := by
          intro v hv
          have h1 := hX v
          have h2 := hY v
          rw [mem_filter, mem_compl]
          rcases mem_union.1 hv with hv | hv
          · rw [hP2, mem_filter] at hv
            obtain ⟨-, hc, hyv, hzv⟩ := hv
            refine ⟨?_, hzv, hc⟩
            simp only [hP1, hN2, mem_union, mem_filter, mem_univ, true_and, not_or]
            exact ⟨⟨⟨fun h => hyv h.2.1, fun h => hc h.1⟩, fun h => hyv (h1 h).2.1⟩,
              fun h => hc (h2 h).1⟩
          · rw [mem_sdiff, hP12, mem_filter] at hv
            obtain ⟨⟨-, hc, hyv, hzv⟩, hvX⟩ := hv
            refine ⟨?_, hzv, hc⟩
            simp only [hP1, hN2, mem_union, mem_filter, mem_univ, true_and, not_or]
            exact ⟨⟨⟨fun h => h.2.2 hzv, fun h => hc h.1⟩, hvX⟩, fun h => hc (h2 h).1⟩
        have dj : Disjoint P2 (P12 \ X) := by
          rw [disjoint_left]
          intro v h1 h2
          rw [hP2, mem_filter] at h1
          rw [mem_sdiff, hP12, mem_filter] at h2
          exact h1.2.2.1 h2.1.2.2.1
        have := card_le_card e3
        have := card_le_card e4
        rw [card_union_of_disjoint dj] at this
        have := card_sdiff_add_card_eq_card hYB
        have := card_sdiff_add_card_eq_card hXP
        omega

end Approval

end HHRControl.PV

open HHRControl.PV CookPvsNP Finset

theorem solution :
    (VulnerableDC .TE approval ∧ CertVulnerableDC .TE approval) ∧
      (VulnerableDC .TP approval ∧ CertVulnerableDC .TP approval) := by
  have susc_apte : SusceptibleDC .TE approval := example_4_11.2.1
  have lang_apte : dcLang .TE approval = { w : List ProjSchedTW.Complexity.BSym |
      ∃ (m n : ℕ) (c : Fin m) (P : Fin n → Approval m),
        (∃ y z : Fin m, y ≠ c ∧ z ≠ c ∧
          (univ.filter fun v => c ∈ P v ∧ y ∉ P v ∧ z ∉ P v).card ≤
            (univ.filter fun v => c ∉ P v ∧ (y ∈ P v ∨ z ∈ P v)).card) ∧
        w = electionCode approval c P } := by
    ext w
    simp only [dcLang, Set.mem_setOf_eq]
    constructor
    · rintro ⟨m, n, c, P, h, rfl⟩
      exact ⟨m, n, c, P, (dcpv_approval_TE_iff P c).1 h, rfl⟩
    · rintro ⟨m, n, c, P, h, rfl⟩
      exact ⟨m, n, c, P, (dcpv_approval_TE_iff P c).2 h, rfl⟩
  obtain ⟨f_apte, hf_apte, hspec_apte⟩ := approval_te_dc_certifier
  have r_apte : VulnerableDC .TE approval ∧ CertVulnerableDC .TE approval := by
    refine ⟨⟨susc_apte, ?_⟩, susc_apte, f_apte, hf_apte, fun m n c P => ⟨fun h => ?_, fun h => ?_⟩⟩
    · rw [lang_apte]; exact approval_te_dc_criterion_mem_P
    · exact (hspec_apte m n c P).1 ((dcpv_approval_TE_iff P c).1 h)
    · exact (hspec_apte m n c P).2 (fun h' => h ((dcpv_approval_TE_iff P c).2 h'))
  have susc_aptp : SusceptibleDC .TP approval := example_4_11.2.2
  have lang_aptp : dcLang .TP approval = { w : List ProjSchedTW.Complexity.BSym |
      ∃ (m n : ℕ) (c : Fin m) (P : Fin n → Approval m),
        ((∃ x : Fin m, x ≠ c ∧ approvalScore P univ c ≤ approvalScore P univ x) ∨
          ∃ y z : Fin m, y ≠ c ∧ z ≠ c ∧
            (univ.filter fun v => c ∈ P v ∧ y ∉ P v ∧ z ∉ P v).card + 2 ≤
              (univ.filter fun v => c ∉ P v ∧ (y ∈ P v ∨ z ∈ P v)).card ∧
            1 ≤ (univ.filter fun v => c ∉ P v ∧ y ∈ P v).card ∧
            1 ≤ (univ.filter fun v => c ∉ P v ∧ z ∈ P v).card) ∧
        w = electionCode approval c P } := by
    ext w
    simp only [dcLang, Set.mem_setOf_eq]
    constructor
    · rintro ⟨m, n, c, P, h, rfl⟩
      exact ⟨m, n, c, P, (dcpv_approval_TP_iff P c).1 h, rfl⟩
    · rintro ⟨m, n, c, P, h, rfl⟩
      exact ⟨m, n, c, P, (dcpv_approval_TP_iff P c).2 h, rfl⟩
  obtain ⟨f_aptp, hf_aptp, hspec_aptp⟩ := approval_tp_dc_certifier
  have r_aptp : VulnerableDC .TP approval ∧ CertVulnerableDC .TP approval := by
    refine ⟨⟨susc_aptp, ?_⟩, susc_aptp, f_aptp, hf_aptp, fun m n c P => ⟨fun h => ?_, fun h => ?_⟩⟩
    · rw [lang_aptp]; exact approval_tp_dc_criterion_mem_P
    · exact (hspec_aptp m n c P).1 ((dcpv_approval_TP_iff P c).1 h)
    · exact (hspec_aptp m n c P).2 (fun h' => h ((dcpv_approval_TP_iff P c).2 h'))
  exact ⟨r_apte, r_aptp⟩
