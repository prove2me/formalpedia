-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.Pruning.lemma_3_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-13T21:10:43.406703+00:00
-- url     : https://prove2.me/submissions/6d3d050d-0e5e-4fa6-8d6c-4074419628bf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_SeymourSecondNeighborhood_Image
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_konig
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_matching_bound

set_option autoImplicit false
open Finset

namespace OAI.SeymourSecondNeighborhood.Sol_OAI_SeymourSecondNeighborhood_Pruning_lemma_3_1

open OAI.SeymourSecondNeighborhood.Pruning

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The vertex type of the augmented bipartite graph `Γ` (used for both sides):
`inl` = a member of `R` (resp. `C`), `inr` = a copy of a point of `Z`. -/
abbrev V (X : Type*) := (X × X) ⊕ (X × X)

/-- The edge predicate of `Γ`: conflict edges, left-cover edges and right-cover edges. -/
def EdgeP (arrow : X → X → Prop) (R C : Finset (X × X)) (e : V X × V X) : Prop :=
  (∃ l ∈ R, ∃ c ∈ C, e = (Sum.inl l, Sum.inl c) ∧ Conflict arrow l c) ∨
  (∃ l ∈ R, ∃ z ∈ pointsZ arrow R C, e = (Sum.inl l, Sum.inr z) ∧ CoversL arrow l z) ∨
  (∃ z ∈ pointsZ arrow R C, ∃ c ∈ C, e = (Sum.inr z, Sum.inl c) ∧ CoversR arrow c z)

/-- The edge set of `Γ` as a finset. -/
noncomputable def gammaEdges (arrow : X → X → Prop) (R C : Finset (X × X)) :
    Finset (V X × V X) := by
  classical
  exact univ.filter (EdgeP arrow R C)

theorem mem_gammaEdges {arrow : X → X → Prop} {R C : Finset (X × X)} {e : V X × V X} :
    e ∈ gammaEdges arrow R C ↔ EdgeP arrow R C e := by
  unfold gammaEdges
  simp only [mem_filter, mem_univ, true_and]

omit [Fintype X] in
theorem mem_pointsZ_iff {arrow : X → X → Prop} {R C : Finset (X × X)} {z : X × X} :
    z ∈ pointsZ arrow R C ↔ ∃ l ∈ R, ∃ c ∈ C, Conflict arrow l c ∧ z = (c.1, l.2) := by
  unfold pointsZ conflicts
  simp only [mem_image, mem_filter, mem_product]
  constructor
  · rintro ⟨⟨l, c⟩, hlc, rfl⟩
    exact ⟨l, hlc.1.1, c, hlc.1.2, hlc.2, rfl⟩
  · rintro ⟨l, hl, c, hc, hconf, rfl⟩
    exact ⟨(l, c), ⟨⟨hl, hc⟩, hconf⟩, rfl⟩

theorem mem_uncovered_iff {arrow : X → X → Prop} {R C R' C' : Finset (X × X)} {z : X × X} :
    z ∈ uncovered arrow R C R' C' ↔
      z ∈ pointsZ arrow R C ∧
        (∀ l ∈ R', ¬ CoversL arrow l z) ∧ (∀ c ∈ C', ¬ CoversR arrow c z) := by
  unfold uncovered
  simp only [mem_filter]

omit [Fintype X] in
/-- A member of `R` conflicting with nothing in `C` is isolated in `Γ` (on the left). -/
theorem not_edge_fst_of_free (arrow : X → X → Prop) (R C : Finset (X × X)) (l : X × X)
    (hfree : ∀ c ∈ C, ¬ Conflict arrow l c) (e : V X × V X) (he : EdgeP arrow R C e) :
    e.1 ≠ Sum.inl l := by
  rcases he with ⟨l', _, c, hc, rfl, hconf⟩ | ⟨l', _, z, hz, rfl, hcov⟩ | ⟨z, _, c, _, rfl, _⟩
  · intro h
    have h' : l' = l := Sum.inl.inj h
    subst h'
    exact hfree c hc hconf
  · intro h
    have h' : l' = l := Sum.inl.inj h
    subst h'
    obtain ⟨l0, _, c0, hc0, hconf0, rfl⟩ := mem_pointsZ_iff.1 hz
    obtain ⟨h1, h2⟩ := hcov
    simp only at h1 h2
    refine hfree c0 hc0 ⟨h2, ?_⟩
    rw [← h1]
    exact hconf0.2
  · simp

omit [Fintype X] in
/-- A member of `C` conflicting with nothing in `R` is isolated in `Γ` (on the right). -/
theorem not_edge_snd_of_free (arrow : X → X → Prop) (R C : Finset (X × X)) (c : X × X)
    (hfree : ∀ l ∈ R, ¬ Conflict arrow l c) (e : V X × V X) (he : EdgeP arrow R C e) :
    e.2 ≠ Sum.inl c := by
  rcases he with ⟨l, hl, c', _, rfl, hconf⟩ | ⟨l, _, z, _, rfl, _⟩ | ⟨z, hz, c', _, rfl, hcov⟩
  · intro h
    have h' : c' = c := Sum.inl.inj h
    subst h'
    exact hfree l hl hconf
  · simp
  · intro h
    have h' : c' = c := Sum.inl.inj h
    subst h'
    obtain ⟨l0, hl0, c0, _, hconf0, rfl⟩ := mem_pointsZ_iff.1 hz
    obtain ⟨h1, h2⟩ := hcov
    simp only at h1 h2
    refine hfree l0 hl0 ⟨?_, h2⟩
    rw [← h1]
    exact hconf0.1

/-- The counting part of the glue. -/
theorem count_bound (arrow : X → X → Prop) (R C : Finset (X × X)) (KA' KB' : Finset (V X))
    (hcov : ∀ e ∈ gammaEdges arrow R C, e.1 ∈ KA' ∨ e.2 ∈ KB')
    (hcard : KA'.card + KB'.card ≤ (pointsZ arrow R C).card + (pointsH arrow R C).card) :
    (R \ R.filter (fun l => Sum.inl l ∉ KA')).card
        + (C \ C.filter (fun c => Sum.inl c ∉ KB')).card
      ≤ (pointsH arrow R C).card
        + (uncovered arrow R C (R.filter (fun l => Sum.inl l ∉ KA'))
            (C.filter (fun c => Sum.inl c ∉ KB'))).card := by
  classical
  have hDA : R \ R.filter (fun l => Sum.inl l ∉ KA') = R.filter (fun l => Sum.inl l ∈ KA') := by
    ext l
    simp only [mem_sdiff, mem_filter, not_and, not_not]
    tauto
  have hDB : C \ C.filter (fun c => Sum.inl c ∉ KB') = C.filter (fun c => Sum.inl c ∈ KB') := by
    ext c
    simp only [mem_sdiff, mem_filter, not_and, not_not]
    tauto
  rw [hDA, hDB]
  -- claim 1
  have h1 : (R.filter (fun l => Sum.inl l ∈ KA')).card
      + ((pointsZ arrow R C).filter (fun z => Sum.inr z ∈ KA')).card ≤ KA'.card := by
    have hsub : (R.filter (fun l => Sum.inl l ∈ KA')).image Sum.inl
        ∪ ((pointsZ arrow R C).filter (fun z => Sum.inr z ∈ KA')).image Sum.inr ⊆ KA' := by
      intro a ha
      rcases mem_union.1 ha with h | h
      · obtain ⟨l, hl, rfl⟩ := mem_image.1 h
        exact (mem_filter.1 hl).2
      · obtain ⟨z, hz, rfl⟩ := mem_image.1 h
        exact (mem_filter.1 hz).2
    have hdisj : Disjoint ((R.filter (fun l => Sum.inl l ∈ KA')).image Sum.inl)
        (((pointsZ arrow R C).filter (fun z => Sum.inr z ∈ KA')).image Sum.inr) := by
      rw [disjoint_left]
      intro a ha hb
      obtain ⟨l, _, rfl⟩ := mem_image.1 ha
      obtain ⟨z, _, hz⟩ := mem_image.1 hb
      exact Sum.inr_ne_inl hz
    have := card_le_card hsub
    rwa [card_union_of_disjoint hdisj, card_image_of_injective _ Sum.inl_injective,
      card_image_of_injective _ Sum.inr_injective] at this
  -- claim 2
  have h2 : (C.filter (fun c => Sum.inl c ∈ KB')).card
      + ((pointsZ arrow R C).filter (fun z => Sum.inr z ∈ KB')).card ≤ KB'.card := by
    have hsub : (C.filter (fun c => Sum.inl c ∈ KB')).image Sum.inl
        ∪ ((pointsZ arrow R C).filter (fun z => Sum.inr z ∈ KB')).image Sum.inr ⊆ KB' := by
      intro a ha
      rcases mem_union.1 ha with h | h
      · obtain ⟨c, hc, rfl⟩ := mem_image.1 h
        exact (mem_filter.1 hc).2
      · obtain ⟨z, hz, rfl⟩ := mem_image.1 h
        exact (mem_filter.1 hz).2
    have hdisj : Disjoint ((C.filter (fun c => Sum.inl c ∈ KB')).image Sum.inl)
        (((pointsZ arrow R C).filter (fun z => Sum.inr z ∈ KB')).image Sum.inr) := by
      rw [disjoint_left]
      intro a ha hb
      obtain ⟨c, _, rfl⟩ := mem_image.1 ha
      obtain ⟨z, _, hz⟩ := mem_image.1 hb
      exact Sum.inr_ne_inl hz
    have := card_le_card hsub
    rwa [card_union_of_disjoint hdisj, card_image_of_injective _ Sum.inl_injective,
      card_image_of_injective _ Sum.inr_injective] at this
  -- claim 3: every point of `Z` is uncovered or has a copy in the cover
  have h3 : (pointsZ arrow R C).card
      ≤ (uncovered arrow R C (R.filter (fun l => Sum.inl l ∉ KA'))
            (C.filter (fun c => Sum.inl c ∉ KB'))).card
        + ((pointsZ arrow R C).filter (fun z => Sum.inr z ∈ KA')).card
        + ((pointsZ arrow R C).filter (fun z => Sum.inr z ∈ KB')).card := by
    have hsub : pointsZ arrow R C ⊆
        uncovered arrow R C (R.filter (fun l => Sum.inl l ∉ KA'))
            (C.filter (fun c => Sum.inl c ∉ KB'))
        ∪ (pointsZ arrow R C).filter (fun z => Sum.inr z ∈ KA')
        ∪ (pointsZ arrow R C).filter (fun z => Sum.inr z ∈ KB') := by
      intro z hz
      by_cases hL : ∃ l ∈ R.filter (fun l => Sum.inl l ∉ KA'), CoversL arrow l z
      · obtain ⟨l, hl, hcovl⟩ := hL
        rw [mem_filter] at hl
        have he : (Sum.inl l, Sum.inr z) ∈ gammaEdges arrow R C :=
          mem_gammaEdges.2 (Or.inr (Or.inl ⟨l, hl.1, z, hz, rfl, hcovl⟩))
        rcases hcov _ he with h | h
        · exact absurd h hl.2
        · exact mem_union.2 (Or.inr (mem_filter.2 ⟨hz, h⟩))
      · by_cases hR : ∃ c ∈ C.filter (fun c => Sum.inl c ∉ KB'), CoversR arrow c z
        · obtain ⟨c, hc, hcovc⟩ := hR
          rw [mem_filter] at hc
          have he : (Sum.inr z, Sum.inl c) ∈ gammaEdges arrow R C :=
            mem_gammaEdges.2 (Or.inr (Or.inr ⟨z, hz, c, hc.1, rfl, hcovc⟩))
          rcases hcov _ he with h | h
          · exact mem_union.2 (Or.inl (mem_union.2 (Or.inr (mem_filter.2 ⟨hz, h⟩))))
          · exact absurd h hc.2
        · refine mem_union.2 (Or.inl (mem_union.2 (Or.inl ?_)))
          rw [mem_uncovered_iff]
          exact ⟨hz, fun l hl h => hL ⟨l, hl, h⟩, fun c hc h => hR ⟨c, hc, h⟩⟩
    calc (pointsZ arrow R C).card ≤ _ := card_le_card hsub
      _ ≤ _ := card_union_le _ _
      _ ≤ _ := Nat.add_le_add_right (card_union_le _ _) _
  omega

theorem main (arrow : X → X → Prop) (R C : Finset (X × X)) :
    ∃ R' ⊆ R, ∃ C' ⊆ C,
      (∀ l ∈ R', ∀ c ∈ C', ¬ Conflict arrow l c) ∧
      (∀ l ∈ R, (∀ c ∈ C, ¬ Conflict arrow l c) → l ∈ R') ∧
      (∀ c ∈ C, (∀ l ∈ R, ¬ Conflict arrow l c) → c ∈ C') ∧
      (R \ R').card + (C \ C').card
        ≤ (pointsH arrow R C).card + (uncovered arrow R C R' C').card := by
  classical
  -- Kőnig applied to `Γ`, with the matching bound
  obtain ⟨KA, KB, hcov, hcard⟩ := konig (gammaEdges arrow R C)
    ((pointsZ arrow R C).card + (pointsH arrow R C).card) (by
      intro M hM h1 h2
      exact matching_bound arrow R C M (fun e he => mem_gammaEdges.1 (hM he)) h1 h2)
  -- remove isolated vertices from the cover
  set KA' := KA.filter (fun a => ∃ e ∈ gammaEdges arrow R C, e.1 = a) with hKA'
  set KB' := KB.filter (fun b => ∃ e ∈ gammaEdges arrow R C, e.2 = b) with hKB'
  have hcov' : ∀ e ∈ gammaEdges arrow R C, e.1 ∈ KA' ∨ e.2 ∈ KB' := by
    intro e he
    rcases hcov e he with h | h
    · exact Or.inl (mem_filter.2 ⟨h, e, he, rfl⟩)
    · exact Or.inr (mem_filter.2 ⟨h, e, he, rfl⟩)
  have hcard' : KA'.card + KB'.card ≤ (pointsZ arrow R C).card + (pointsH arrow R C).card :=
    le_trans (Nat.add_le_add (card_le_card (filter_subset _ _))
      (card_le_card (filter_subset _ _))) hcard
  refine ⟨R.filter (fun l => Sum.inl l ∉ KA'), filter_subset _ _,
    C.filter (fun c => Sum.inl c ∉ KB'), filter_subset _ _, ?_, ?_, ?_, ?_⟩
  · intro l hl c hc hconf
    rw [mem_filter] at hl hc
    have he : (Sum.inl l, Sum.inl c) ∈ gammaEdges arrow R C :=
      mem_gammaEdges.2 (Or.inl ⟨l, hl.1, c, hc.1, rfl, hconf⟩)
    rcases hcov' _ he with h | h
    · exact hl.2 h
    · exact hc.2 h
  · intro l hl hfree
    rw [mem_filter]
    refine ⟨hl, fun hmem => ?_⟩
    rw [mem_filter] at hmem
    obtain ⟨_, e, he, he1⟩ := hmem
    exact not_edge_fst_of_free arrow R C l hfree e (mem_gammaEdges.1 he) he1
  · intro c hc hfree
    rw [mem_filter]
    refine ⟨hc, fun hmem => ?_⟩
    rw [mem_filter] at hmem
    obtain ⟨_, e, he, he2⟩ := hmem
    exact not_edge_snd_of_free arrow R C c hfree e (mem_gammaEdges.1 he) he2
  · exact count_bound arrow R C KA' KB' hcov' hcard'

end OAI.SeymourSecondNeighborhood.Sol_OAI_SeymourSecondNeighborhood_Pruning_lemma_3_1

open OAI.SeymourSecondNeighborhood in
open OAI.SeymourSecondNeighborhood.Pruning in
theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    (arrow : X → X → Prop) (R C : Finset (X × X)) :
    ∃ R' ⊆ R, ∃ C' ⊆ C,
      (∀ l ∈ R', ∀ c ∈ C', ¬ Conflict arrow l c) ∧
      (∀ l ∈ R, (∀ c ∈ C, ¬ Conflict arrow l c) → l ∈ R') ∧
      (∀ c ∈ C, (∀ l ∈ R, ¬ Conflict arrow l c) → c ∈ C') ∧
      (R \ R').card + (C \ C').card
        ≤ (pointsH arrow R C).card + (uncovered arrow R C R' C').card :=
  OAI.SeymourSecondNeighborhood.Sol_OAI_SeymourSecondNeighborhood_Pruning_lemma_3_1.main arrow R C
