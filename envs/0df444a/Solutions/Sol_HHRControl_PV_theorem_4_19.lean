-- Prove2me | solution 1 for HHRControl.PV.theorem_4_19
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:15:26.971343+00:00
-- url     : https://prove2.me/submissions/90ea221d-83ab-4709-b027-0d83ee390c9e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages
import Theorems.Thm_HHRControl_PV_example_4_9
import Theorems.Thm_HHRControl_PV_plurality_te_dc_criterion_mem_P
import Theorems.Thm_HHRControl_PV_plurality_te_dc_certifier

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

/-! ## Plurality voting, model TE -/

section Plurality

variable {m n : ℕ} (P : Fin n → Ranking m)

theorem top_unique {v : Fin n} {x x' : Fin m}
    (h1 : ∀ y ∈ (univ : Finset (Fin m)), y ≠ x → P v x < P v y)
    (h2 : ∀ y ∈ (univ : Finset (Fin m)), y ≠ x' → P v x' < P v y) : x = x' := by
  by_contra h
  have a := h1 x' (mem_univ _) (Ne.symm h)
  have b := h2 x (mem_univ _) h
  exact lt_asymm a b

theorem plurality_winners_eq (D : Finset (Fin m)) (U : Finset (Fin n)) :
    plurality.winners m n P D U =
      D.filter fun x => ∀ y ∈ D, pluralityScore P D U y ≤ pluralityScore P D U x := by
  ext x; simp [plurality]

theorem mem_nominees_TE_plurality (U : Finset (Fin n)) (c : Fin m) :
    c ∈ nominees .TE plurality P U ↔
      ∀ y, y ≠ c → pluralityScore P univ U y < pluralityScore P univ U c := by
  simp only [nominees]
  rw [plurality_winners_eq]
  convert mem_unique_max_iff (fun x => pluralityScore P univ U x) c

theorem nominees_TE_plurality_cases (U : Finset (Fin n)) :
    nominees .TE plurality P U = ∅ ∨ ∃ w, nominees .TE plurality P U = {w} := by
  simp only [nominees]
  rw [plurality_winners_eq]
  split_ifs with hc
  · exact Or.inr (card_eq_one.1 hc)
  · exact Or.inl rfl

theorem nominees_TE_plurality_eq_of_mem (U : Finset (Fin n)) (c : Fin m)
    (h : c ∈ nominees .TE plurality P U) : nominees .TE plurality P U = {c} := by
  rcases nominees_TE_plurality_cases P U with h0 | ⟨w, hw⟩
  · rw [h0] at h; simp at h
  · rw [hw, mem_singleton] at h; rw [hw, h]

theorem twoStage_plurality_eq_singleton (V₁ : Finset (Fin n)) (c : Fin m) :
    twoStage .TE plurality P V₁ = {c} ↔
      c ∈ nominees .TE plurality P V₁ ∪ nominees .TE plurality P V₁ᶜ ∧
        ∀ y ∈ nominees .TE plurality P V₁ ∪ nominees .TE plurality P V₁ᶜ, y ≠ c →
          pluralityScore P (nominees .TE plurality P V₁ ∪ nominees .TE plurality P V₁ᶜ) univ y <
            pluralityScore P (nominees .TE plurality P V₁ ∪ nominees .TE plurality P V₁ᶜ) univ c := by
  unfold twoStage
  rw [plurality_winners_eq]
  convert filter_max_eq_singleton (nominees .TE plurality P V₁ ∪ nominees .TE plurality P V₁ᶜ)
    (fun x => pluralityScore P (nominees .TE plurality P V₁ ∪ nominees .TE plurality P V₁ᶜ)
      univ x) c

theorem pair_score {a b : Fin m} (hab : a ≠ b) :
    pluralityScore P ({a} ∪ {b}) univ a = prefCount P univ a b := by
  unfold pluralityScore prefCount
  congr 1
  ext v
  simp only [mem_filter, mem_univ, true_and, mem_union, mem_singleton]
  constructor
  · intro h; exact h b (Or.inr rfl) (Ne.symm hab)
  · rintro h y (rfl | rfl) hy
    · exact absurd rfl hy
    · exact h

theorem score_split (V₁ : Finset (Fin n)) (x : Fin m) :
    pluralityScore P univ V₁ x + pluralityScore P univ V₁ᶜ x = pluralityScore P univ univ x :=
  split_count _ V₁

/-- If `c` is nominated by `U`, and the third alternative of the criterion fails, `c` wins. -/
theorem final_of_mem (U : Finset (Fin n)) (c : Fin m)
    (Hc : ∀ x, x ≠ c → 1 ≤ pluralityScore P univ univ c → 1 ≤ pluralityScore P univ univ x →
      prefCount P univ c x ≤ prefCount P univ x c →
      ∃ t, t ≠ c ∧ t ≠ x ∧
        pluralityScore P univ univ c + pluralityScore P univ univ x <
          pluralityScore P univ univ t + 2)
    (hU : c ∈ nominees .TE plurality P U) :
    c ∈ nominees .TE plurality P U ∪ nominees .TE plurality P Uᶜ ∧
      ∀ y ∈ nominees .TE plurality P U ∪ nominees .TE plurality P Uᶜ, y ≠ c →
        pluralityScore P (nominees .TE plurality P U ∪ nominees .TE plurality P Uᶜ) univ y <
          pluralityScore P (nominees .TE plurality P U ∪ nominees .TE plurality P Uᶜ) univ c := by
  have hsU := (mem_nominees_TE_plurality P U c).1 hU
  rw [nominees_TE_plurality_eq_of_mem P U c hU]
  rcases nominees_TE_plurality_cases P Uᶜ with h0 | ⟨w, hw⟩
  · rw [h0]
    refine ⟨by simp, fun y hy hyc => ?_⟩
    simp at hy; exact absurd hy hyc
  · rw [hw]
    by_cases hwc : w = c
    · subst hwc
      refine ⟨by simp, fun y hy hyc => ?_⟩
      simp at hy; exact absurd hy hyc
    · have hsW := (mem_nominees_TE_plurality P Uᶜ w).1 (by rw [hw]; exact mem_singleton_self w)
      refine ⟨by simp, fun y hy hyc => ?_⟩
      have hyw : y = w := by
        simp only [mem_union, mem_singleton] at hy; tauto
      subst hyw
      rw [pair_score P (Ne.symm hwc), union_comm, pair_score P hwc]
      by_contra hle
      push Not at hle
      have a1 := hsU y hwc
      have a2 := hsW c (Ne.symm hwc)
      have sc := score_split P U c
      have sy := score_split P U y
      obtain ⟨t, htc, hty, ht⟩ := Hc y hwc (by omega) (by omega) hle
      have b1 := hsU t htc
      have b2 := hsW t hty
      have st := score_split P U t
      omega

/-- Destructive control by partition of voters, plurality voting, model TE (Theorem 4.19). -/
theorem dcpv_plurality_TE_iff (c : Fin m) :
    DCPV .TE plurality P c ↔
      (∃ y, y ≠ c ∧ pluralityScore P univ univ c ≤ pluralityScore P univ univ y) ∨
      (∃ y z, y ≠ c ∧ z ≠ c ∧ y ≠ z ∧
        pluralityScore P univ univ c ≤
          pluralityScore P univ univ y + pluralityScore P univ univ z) ∨
      (∃ x, x ≠ c ∧ 1 ≤ pluralityScore P univ univ c ∧ 1 ≤ pluralityScore P univ univ x ∧
        prefCount P univ c x ≤ prefCount P univ x c ∧
        ∀ t, t ≠ c → t ≠ x →
          pluralityScore P univ univ t + 2 ≤
            pluralityScore P univ univ c + pluralityScore P univ univ x) := by
  constructor
  · rintro ⟨V₁, hV₁⟩
    by_contra H
    have Hc : ∀ x, x ≠ c → 1 ≤ pluralityScore P univ univ c → 1 ≤ pluralityScore P univ univ x →
        prefCount P univ c x ≤ prefCount P univ x c →
        ∃ t, t ≠ c ∧ t ≠ x ∧
          pluralityScore P univ univ c + pluralityScore P univ univ x <
            pluralityScore P univ univ t + 2 := by
      intro x hx h1 h2 h3
      by_contra hn
      push Not at hn
      exact H (Or.inr (Or.inr ⟨x, hx, h1, h2, h3, fun t ht1 ht2 => hn t ht1 ht2⟩))
    apply hV₁
    rw [twoStage_plurality_eq_singleton]
    by_cases h1 : c ∈ nominees .TE plurality P V₁
    · exact final_of_mem P V₁ c Hc h1
    by_cases h2 : c ∈ nominees .TE plurality P V₁ᶜ
    · have := final_of_mem P V₁ᶜ c Hc h2
      rw [compl_compl, union_comm] at this
      exact this
    exfalso
    rw [mem_nominees_TE_plurality] at h1 h2
    push Not at h1 h2
    obtain ⟨y, hy, k1⟩ := h1
    obtain ⟨z, hz, k2⟩ := h2
    have sc := score_split P V₁ c
    have sy := score_split P V₁ y
    have sz := score_split P V₁ z
    by_cases hyz : y = z
    · subst hyz
      exact H (Or.inl ⟨y, hy, by omega⟩)
    · exact H (Or.inr (Or.inl ⟨y, z, hy, hz, hyz, by omega⟩))
  · have notD : ∀ V₁ : Finset (Fin n),
        c ∉ nominees .TE plurality P V₁ → c ∉ nominees .TE plurality P V₁ᶜ →
        twoStage .TE plurality P V₁ ≠ {c} := by
      intro V₁ h1 h2 hEq
      rw [twoStage_plurality_eq_singleton] at hEq
      rcases mem_union.1 hEq.1 with h | h
      · exact h1 h
      · exact h2 h
    rintro (⟨y, hy, hle⟩ | ⟨y, z, hy, hz, hyz, hle⟩ | ⟨x, hx, h1, h2, h3, h4⟩)
    · refine ⟨univ, notD univ ?_ ?_⟩
      · rw [mem_nominees_TE_plurality]
        intro h; have := h y hy; omega
      · rw [mem_nominees_TE_plurality]
        intro h; have := h y hy
        simp [pluralityScore] at this
    · obtain ⟨C, hCs, hCc⟩ := exists_subset_card_eq
        (show min (pluralityScore P univ univ c) (pluralityScore P univ univ y) ≤
          (univ.filter fun v => ∀ w ∈ (univ : Finset (Fin m)), w ≠ c → P v c < P v w).card from
          min_le_left _ _)
      have hC : ∀ v ∈ C, ∀ w ∈ (univ : Finset (Fin m)), w ≠ c → P v c < P v w := fun v hv => by
        have := hCs hv; rw [mem_filter] at this; exact this.2
      set V₁ := (univ.filter fun v => ∀ w ∈ (univ : Finset (Fin m)), w ≠ y → P v y < P v w) ∪ C
        with hV₁
      refine ⟨V₁, notD V₁ ?_ ?_⟩
      · rw [mem_nominees_TE_plurality]
        intro h
        have k := h y hy
        have e1 : (V₁.filter fun v => ∀ w ∈ (univ : Finset (Fin m)), w ≠ c → P v c < P v w) ⊆ C := by
          intro v hv
          rw [mem_filter, hV₁, mem_union, mem_filter] at hv
          rcases hv.1 with h' | h'
          · exact absurd (top_unique P h'.2 hv.2) hy
          · exact h'
        have e2 : (univ.filter fun v => ∀ w ∈ (univ : Finset (Fin m)), w ≠ y → P v y < P v w) ⊆
            (V₁.filter fun v => ∀ w ∈ (univ : Finset (Fin m)), w ≠ y → P v y < P v w) := by
          intro v hv
          rw [mem_filter] at hv ⊢
          exact ⟨mem_union_left _ (mem_filter.2 hv), hv.2⟩
        have c1 := card_le_card e1
        have c2 := card_le_card e2
        have := min_le_right (pluralityScore P univ univ c) (pluralityScore P univ univ y)
        unfold pluralityScore at k this hCc
        omega
      · rw [mem_nominees_TE_plurality]
        intro h
        have k := h z hz
        have e3 : (V₁ᶜ.filter fun v => ∀ w ∈ (univ : Finset (Fin m)), w ≠ c → P v c < P v w) ⊆
            (univ.filter fun v => ∀ w ∈ (univ : Finset (Fin m)), w ≠ c → P v c < P v w) \ C := by
          intro v hv
          rw [mem_filter, mem_compl, hV₁, mem_union, not_or] at hv
          rw [mem_sdiff, mem_filter]
          exact ⟨⟨mem_univ _, hv.2⟩, hv.1.2⟩
        have e4 : (univ.filter fun v => ∀ w ∈ (univ : Finset (Fin m)), w ≠ z → P v z < P v w) ⊆
            (V₁ᶜ.filter fun v => ∀ w ∈ (univ : Finset (Fin m)), w ≠ z → P v z < P v w) := by
          intro v hv
          rw [mem_filter] at hv ⊢
          refine ⟨?_, hv.2⟩
          rw [mem_compl, hV₁, mem_union, not_or, mem_filter]
          refine ⟨fun h' => hyz (top_unique P h'.2 hv.2), fun h' => hz ?_⟩
          exact top_unique P hv.2 (hC v h')
        have c3 := card_le_card e3
        have c4 := card_le_card e4
        have c5 := card_sdiff_add_card_eq_card hCs
        unfold pluralityScore at k hle hCc
        omega
    · have hT : ∀ t : Fin m, ∃ T ⊆ (univ.filter fun v =>
          ∀ w ∈ (univ : Finset (Fin m)), w ≠ t → P v t < P v w),
          T.card = if t = c ∨ t = x then 0 else
            min (pluralityScore P univ univ t) (pluralityScore P univ univ c - 1) := by
        intro t
        apply exists_subset_card_eq
        split_ifs
        · exact Nat.zero_le _
        · exact min_le_left _ _
      choose T hTs hTc using hT
      have hTt : ∀ t, ∀ v ∈ T t, ∀ w ∈ (univ : Finset (Fin m)), w ≠ t → P v t < P v w :=
        fun t v hv => by have := hTs t hv; rw [mem_filter] at this; exact this.2
      have hTc0 : T c = ∅ := card_eq_zero.1 (by rw [hTc c, if_pos (Or.inl rfl)])
      have hTx0 : T x = ∅ := card_eq_zero.1 (by rw [hTc x, if_pos (Or.inr rfl)])
      set V₁ := (univ.filter fun v => ∀ w ∈ (univ : Finset (Fin m)), w ≠ c → P v c < P v w) ∪
        univ.biUnion T with hV₁
      have hmem : ∀ v, v ∈ V₁ ↔ (∀ w ∈ (univ : Finset (Fin m)), w ≠ c → P v c < P v w) ∨
          ∃ t, v ∈ T t := by
        intro v; simp [hV₁]
      have hc1 : c ∈ nominees .TE plurality P V₁ := by
        rw [mem_nominees_TE_plurality]
        intro t htc
        have e1 : (univ.filter fun v => ∀ w ∈ (univ : Finset (Fin m)), w ≠ c → P v c < P v w) ⊆
            (V₁.filter fun v => ∀ w ∈ (univ : Finset (Fin m)), w ≠ c → P v c < P v w) := by
          intro v hv; rw [mem_filter] at hv ⊢; exact ⟨(hmem v).2 (Or.inl hv.2), hv.2⟩
        have e2 : (V₁.filter fun v => ∀ w ∈ (univ : Finset (Fin m)), w ≠ t → P v t < P v w) ⊆ T t := by
          intro v hv
          rw [mem_filter, hmem] at hv
          rcases hv.1 with h' | ⟨t', ht'⟩
          · exact absurd (top_unique P hv.2 h') htc
          · have := top_unique P (hTt t' v ht') hv.2
            subst this; exact ht'
        have c1 := card_le_card e1
        have c2 := card_le_card e2
        have hTle : (T t).card < pluralityScore P univ univ c := by
          rw [hTc t]
          split_ifs with h'
          · omega
          · have := min_le_right (pluralityScore P univ univ t) (pluralityScore P univ univ c - 1)
            omega
        unfold pluralityScore at hTle ⊢
        omega
      have hx2 : x ∈ nominees .TE plurality P V₁ᶜ := by
        rw [mem_nominees_TE_plurality]
        have e1 : (univ.filter fun v => ∀ w ∈ (univ : Finset (Fin m)), w ≠ x → P v x < P v w) ⊆
            (V₁ᶜ.filter fun v => ∀ w ∈ (univ : Finset (Fin m)), w ≠ x → P v x < P v w) := by
          intro v hv
          rw [mem_filter] at hv ⊢
          refine ⟨?_, hv.2⟩
          rw [mem_compl, hmem]
          rintro (h' | ⟨t', ht'⟩)
          · exact hx (top_unique P hv.2 h')
          · have := top_unique P (hTt t' v ht') hv.2
            subst this; rw [hTx0] at ht'; simp at ht'
        have c1 := card_le_card e1
        intro t htx
        by_cases htc : t = c
        · subst htc
          have e2 : (V₁ᶜ.filter fun v => ∀ w ∈ (univ : Finset (Fin m)), w ≠ t → P v t < P v w) = ∅ := by
            ext v
            simp only [mem_filter, mem_compl, notMem_empty, iff_false, not_and]
            intro hv h'
            exact hv ((hmem v).2 (Or.inl h'))
          unfold pluralityScore at h2 ⊢
          rw [e2, card_empty]
          omega
        · have e3 : (V₁ᶜ.filter fun v => ∀ w ∈ (univ : Finset (Fin m)), w ≠ t → P v t < P v w) ⊆
              (univ.filter fun v => ∀ w ∈ (univ : Finset (Fin m)), w ≠ t → P v t < P v w) \ T t := by
            intro v hv
            rw [mem_filter, mem_compl, hmem, not_or] at hv
            rw [mem_sdiff, mem_filter]
            exact ⟨⟨mem_univ _, hv.2⟩, fun h' => hv.1.2 ⟨t, h'⟩⟩
          have c3 := card_le_card e3
          have c4 := card_sdiff_add_card_eq_card (hTs t)
          have h4t := h4 t htc htx
          have hTct := hTc t
          rw [if_neg (by tauto)] at hTct
          have := min_le_left (pluralityScore P univ univ t) (pluralityScore P univ univ c - 1)
          have := min_le_right (pluralityScore P univ univ t) (pluralityScore P univ univ c - 1)
          have hmin : min (pluralityScore P univ univ t) (pluralityScore P univ univ c - 1) =
              pluralityScore P univ univ t ∨
              min (pluralityScore P univ univ t) (pluralityScore P univ univ c - 1) =
              pluralityScore P univ univ c - 1 := by
            rcases le_total (pluralityScore P univ univ t) (pluralityScore P univ univ c - 1) with
              h' | h'
            · exact Or.inl (min_eq_left h')
            · exact Or.inr (min_eq_right h')
          unfold pluralityScore at h4t hTct hmin this h2 ⊢
          omega
      refine ⟨V₁, fun hEq => ?_⟩
      rw [twoStage_plurality_eq_singleton, nominees_TE_plurality_eq_of_mem P V₁ c hc1,
        nominees_TE_plurality_eq_of_mem P V₁ᶜ x hx2] at hEq
      have := hEq.2 x (by simp) hx
      rw [pair_score P (Ne.symm hx), union_comm, pair_score P hx] at this
      omega

end Plurality

end HHRControl.PV

open HHRControl.PV CookPvsNP Finset

theorem solution : VulnerableDC .TE plurality ∧ CertVulnerableDC .TE plurality := by
  have susc_pl : SusceptibleDC .TE plurality := example_4_9.2.2.2
  have lang_pl : dcLang .TE plurality = { w : List ProjSchedTW.Complexity.BSym |
      ∃ (m n : ℕ) (c : Fin m) (P : Fin n → Ranking m),
        ((∃ y, y ≠ c ∧ pluralityScore P univ univ c ≤ pluralityScore P univ univ y) ∨
          (∃ y z, y ≠ c ∧ z ≠ c ∧ y ≠ z ∧
            pluralityScore P univ univ c ≤
              pluralityScore P univ univ y + pluralityScore P univ univ z) ∨
          (∃ x, x ≠ c ∧ 1 ≤ pluralityScore P univ univ c ∧ 1 ≤ pluralityScore P univ univ x ∧
            prefCount P univ c x ≤ prefCount P univ x c ∧
            ∀ t, t ≠ c → t ≠ x →
              pluralityScore P univ univ t + 2 ≤
                pluralityScore P univ univ c + pluralityScore P univ univ x)) ∧
        w = electionCode plurality c P } := by
    ext w
    simp only [dcLang, Set.mem_setOf_eq]
    constructor
    · rintro ⟨m, n, c, P, h, rfl⟩
      exact ⟨m, n, c, P, (dcpv_plurality_TE_iff P c).1 h, rfl⟩
    · rintro ⟨m, n, c, P, h, rfl⟩
      exact ⟨m, n, c, P, (dcpv_plurality_TE_iff P c).2 h, rfl⟩
  obtain ⟨f_pl, hf_pl, hspec_pl⟩ := plurality_te_dc_certifier
  have r_pl : VulnerableDC .TE plurality ∧ CertVulnerableDC .TE plurality := by
    refine ⟨⟨susc_pl, ?_⟩, susc_pl, f_pl, hf_pl, fun m n c P => ⟨fun h => ?_, fun h => ?_⟩⟩
    · rw [lang_pl]; exact plurality_te_dc_criterion_mem_P
    · exact (hspec_pl m n c P).1 ((dcpv_plurality_TE_iff P c).1 h)
    · exact (hspec_pl m n c P).2 (fun h' => h ((dcpv_plurality_TE_iff P c).2 h'))
  exact r_pl
