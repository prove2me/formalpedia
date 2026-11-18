-- Prove2me | solution 1 for HHRControl.PV.theorem_4_20
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T05:39:10.05162+00:00
-- url     : https://prove2.me/submissions/c2c5cd30-0aea-4c71-a77e-1b73337125cd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages
import Theorems.Thm_HHRControl_PV_example_4_10
import Theorems.Thm_HHRControl_PV_condorcet_dc_criterion_mem_P
import Theorems.Thm_HHRControl_PV_condorcet_dc_certifier

namespace HHRControl.PV

open CookPvsNP

open Finset

/-- A Condorcet winner set has at most one element. -/
theorem condorcet_winners_card_le_one {m n : ℕ} (P : Fin n → Ranking m) (U : Finset (Fin n)) :
    (condorcet.winners m n P univ U).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hab
  simp only [condorcet, mem_filter] at ha hb
  have h1 := ha.2 b (mem_univ _) (Ne.symm hab)
  have h2 := hb.2 a (mem_univ _) hab
  omega

/-- Under Condorcet voting the nominees in both tie-handling models are the Condorcet winners. -/
theorem mem_nominees_condorcet (rule : TieRule) {m n : ℕ} (P : Fin n → Ranking m)
    (U : Finset (Fin n)) (x : Fin m) :
    x ∈ nominees rule condorcet P U ↔ x ∈ condorcet.winners m n P univ U := by
  cases rule with
  | TP => rfl
  | TE =>
    simp only [nominees]
    split_ifs with h
    · rfl
    · constructor
      · intro hx; simp at hx
      · intro hx
        exfalso
        have h1 := condorcet_winners_card_le_one P U
        have h2 : 0 < (condorcet.winners m n P univ U).card := card_pos.2 ⟨x, hx⟩
        omega

/-- **Destructive control by partition of voters under Condorcet voting** (proof of Theorem 4.20 of
Hemaspaandra–Hemaspaandra–Rothe): in either tie-handling model, `c` can be made not the unique
winner iff there are `d₁ d₂ ≠ c` such that the voters ranking `c` above both `d₁` and `d₂` are at
most as many as the voters ranking `d₁` or `d₂` above `c`. -/
theorem dcpv_condorcet_iff (rule : TieRule) {m n : ℕ} (P : Fin n → Ranking m) (c : Fin m) :
    DCPV rule condorcet P c ↔ ∃ d₁ d₂ : Fin m, d₁ ≠ c ∧ d₂ ≠ c ∧
      (univ.filter fun v => P v c < P v d₁ ∧ P v c < P v d₂).card ≤
        (univ.filter fun v => P v d₁ < P v c ∨ P v d₂ < P v c).card := by
  have tri : ∀ v d, d ≠ c → P v c < P v d ∨ P v d < P v c := fun v d h =>
    lt_or_gt_of_ne (fun e => h ((P v).injective e).symm)
  have memW : ∀ U : Finset (Fin n), c ∈ condorcet.winners m n P univ U ↔
      ∀ y, y ≠ c → prefCount P U y c < prefCount P U c y := by
    intro U; simp [condorcet]
  constructor
  · rintro ⟨V₁, hV₁⟩
    by_contra H
    push Not at H
    apply hV₁
    have cw : ∀ d, d ≠ c → prefCount P univ d c < prefCount P univ c d := by
      intro d hd
      have := H d d hd hd
      simp only [and_self, or_self] at this
      exact this
    have hcD : c ∈ nominees rule condorcet P V₁ ∪ nominees rule condorcet P V₁ᶜ := by
      by_contra hn
      rw [mem_union, not_or, mem_nominees_condorcet, mem_nominees_condorcet, memW, memW] at hn
      push Not at hn
      obtain ⟨⟨d₁, hd₁, k₁⟩, ⟨d₂, hd₂, k₂⟩⟩ := hn
      have hH := H d₁ d₂ hd₁ hd₂
      unfold prefCount at k₁ k₂
      have s1 : (univ.filter fun v => P v c < P v d₁ ∧ P v c < P v d₂) ⊆
          (V₁.filter fun v => P v c < P v d₁) ∪ (V₁ᶜ.filter fun v => P v c < P v d₂) := by
        intro v hv
        simp only [mem_filter, mem_univ, true_and] at hv
        by_cases hv1 : v ∈ V₁
        · exact mem_union_left _ (mem_filter.2 ⟨hv1, hv.1⟩)
        · exact mem_union_right _ (mem_filter.2 ⟨mem_compl.2 hv1, hv.2⟩)
      have s2 : (V₁.filter fun v => P v d₁ < P v c) ∪ (V₁ᶜ.filter fun v => P v d₂ < P v c) ⊆
          (univ.filter fun v => P v d₁ < P v c ∨ P v d₂ < P v c) := by
        intro v hv
        rcases mem_union.1 hv with h | h <;>
          simp only [mem_filter, mem_univ, true_and] at h ⊢
        · exact Or.inl h.2
        · exact Or.inr h.2
      have dj : Disjoint (V₁.filter fun v => P v d₁ < P v c)
          (V₁ᶜ.filter fun v => P v d₂ < P v c) := by
        rw [disjoint_left]
        intro v h1 h2
        exact (mem_compl.1 (mem_filter.1 h2).1) (mem_filter.1 h1).1
      have c1 := card_le_card s1
      have c2 := card_le_card s2
      rw [card_union_of_disjoint dj] at c2
      have c3 := card_union_le (V₁.filter fun v => P v c < P v d₁)
        (V₁ᶜ.filter fun v => P v c < P v d₂)
      omega
    ext x
    simp only [twoStage, condorcet, mem_filter, mem_singleton]
    constructor
    · rintro ⟨_, hx⟩
      by_contra hxc
      have a1 := hx c hcD (Ne.symm hxc)
      have a2 := cw x hxc
      omega
    · rintro rfl
      exact ⟨hcD, fun y _ hyc => cw y hyc⟩
  · rintro ⟨d₁, d₂, h₁, h₂, hcard⟩
    set A := univ.filter fun v => P v d₁ < P v c with hA
    set B := univ.filter fun v => P v c < P v d₁ ∧ P v c < P v d₂ with hB
    obtain ⟨Y, hYB, hYc⟩ :=
      exists_subset_card_eq (show min B.card A.card ≤ B.card from min_le_left _ _)
    refine ⟨A ∪ Y, fun hEq => ?_⟩
    have hc : c ∈ twoStage rule condorcet P (A ∪ Y) := hEq ▸ mem_singleton_self c
    have hcD : c ∈ nominees rule condorcet P (A ∪ Y) ∪ nominees rule condorcet P (A ∪ Y)ᶜ :=
      Finset.mem_of_mem_filter _ hc
    rcases mem_union.1 hcD with h | h <;> rw [mem_nominees_condorcet, memW] at h
    · have k := h d₁ h₁
      unfold prefCount at k
      have e1 : ((A ∪ Y).filter fun v => P v c < P v d₁) ⊆ Y := by
        intro v hv
        rw [mem_filter, mem_union] at hv
        rcases hv with ⟨hv | hv, hlt⟩
        · rw [hA, mem_filter] at hv
          exact absurd hlt (lt_asymm hv.2)
        · exact hv
      have e2 : A ⊆ ((A ∪ Y).filter fun v => P v d₁ < P v c) := by
        intro v hv
        rw [mem_filter, mem_union]
        exact ⟨Or.inl hv, (mem_filter.1 hv).2⟩
      have := card_le_card e1
      have := card_le_card e2
      have := min_le_right B.card A.card
      omega
    · have k := h d₂ h₂
      unfold prefCount at k
      have e3 : ((A ∪ Y)ᶜ.filter fun v => P v c < P v d₂) ⊆ B \ Y := by
        intro v hv
        rw [mem_filter, mem_compl, mem_union, not_or] at hv
        obtain ⟨⟨hvA, hvY⟩, hlt⟩ := hv
        rw [mem_sdiff]
        refine ⟨?_, hvY⟩
        rw [hB, mem_filter]
        refine ⟨mem_univ _, ?_, hlt⟩
        rcases tri v d₁ h₁ with h' | h'
        · exact h'
        · exact absurd (show v ∈ A from mem_filter.2 ⟨mem_univ v, h'⟩) hvA
      have e4 : (univ.filter fun v => P v d₂ < P v c ∧ ¬ P v d₁ < P v c) ⊆
          ((A ∪ Y)ᶜ.filter fun v => P v d₂ < P v c) := by
        intro v hv
        simp only [mem_filter, mem_univ, true_and] at hv
        rw [mem_filter, mem_compl, mem_union, not_or]
        refine ⟨⟨fun hvA => hv.2 (mem_filter.1 hvA).2, fun hvY => ?_⟩, hv.1⟩
        have := (mem_filter.1 (hYB hvY)).2.2
        exact lt_asymm this hv.1
      have e5 : (univ.filter fun v => P v d₁ < P v c ∨ P v d₂ < P v c) ⊆
          A ∪ (univ.filter fun v => P v d₂ < P v c ∧ ¬ P v d₁ < P v c) := by
        intro v hv
        simp only [mem_filter, mem_univ, true_and] at hv
        by_cases h1 : P v d₁ < P v c
        · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, h1⟩)
        · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, hv.resolve_left h1, h1⟩)
      have := card_le_card e3
      have := card_le_card e4
      have := card_le_card e5
      have := card_union_le A (univ.filter fun v => P v d₂ < P v c ∧ ¬ P v d₁ < P v c)
      have := card_sdiff_add_card_eq_card hYB
      omega


end HHRControl.PV

open HHRControl.PV CookPvsNP Finset

theorem solution (rule : TieRule) :
    VulnerableDC rule condorcet ∧ CertVulnerableDC rule condorcet := by
  have susc : SusceptibleDC rule condorcet := example_4_10.2 rule
  have lang : dcLang rule condorcet = { w : List ProjSchedTW.Complexity.BSym |
      ∃ (m n : ℕ) (c : Fin m) (P : Fin n → Ranking m),
        (∃ d₁ d₂ : Fin m, d₁ ≠ c ∧ d₂ ≠ c ∧
          (univ.filter fun v => P v c < P v d₁ ∧ P v c < P v d₂).card ≤
            (univ.filter fun v => P v d₁ < P v c ∨ P v d₂ < P v c).card) ∧
        w = electionCode condorcet c P } := by
    ext w
    simp only [dcLang, Set.mem_setOf_eq]
    constructor
    · rintro ⟨m, n, c, P, h, rfl⟩
      exact ⟨m, n, c, P, (dcpv_condorcet_iff rule P c).1 h, rfl⟩
    · rintro ⟨m, n, c, P, h, rfl⟩
      exact ⟨m, n, c, P, (dcpv_condorcet_iff rule P c).2 h, rfl⟩
  obtain ⟨f, hf, hspec⟩ := condorcet_dc_certifier
  refine ⟨⟨susc, ?_⟩, susc, f, hf, fun m n c P => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [lang]; exact condorcet_dc_criterion_mem_P
  · obtain ⟨V₁, h1, h2, h3⟩ := (hspec m n c P).1 ((dcpv_condorcet_iff rule P c).1 h)
    refine ⟨V₁, fun hEq => ?_, h3⟩
    have hc : c ∈ twoStage rule condorcet P V₁ := hEq ▸ mem_singleton_self c
    have hcD : c ∈ nominees rule condorcet P V₁ ∪ nominees rule condorcet P V₁ᶜ :=
      Finset.mem_of_mem_filter _ hc
    rcases mem_union.1 hcD with h | h
    · exact h1 ((mem_nominees_condorcet rule P V₁ c).1 h)
    · exact h2 ((mem_nominees_condorcet rule P V₁ᶜ c).1 h)
  · exact (hspec m n c P).2 (fun h' => h ((dcpv_condorcet_iff rule P c).2 h'))
