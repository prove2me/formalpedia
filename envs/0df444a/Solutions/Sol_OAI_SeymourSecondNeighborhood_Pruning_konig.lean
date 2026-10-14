-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.Pruning.konig
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-13T21:09:11.857166+00:00
-- url     : https://prove2.me/submissions/ae6c9541-4447-4c60-bd21-a03f02151bbe

import Mathlib
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_SeymourSecondNeighborhood_Image

set_option autoImplicit false
open Finset

namespace OAI.SeymourSecondNeighborhood.Sol_OAI_SeymourSecondNeighborhood_Pruning_konig

variable {A B : Type*}

/-- The neighbourhood `N(S)` of a set `S` of left vertices in the bipartite graph `E`. -/
noncomputable def nbr (E : Finset (A × B)) (S : Finset A) : Finset B := by
  classical
  exact (E.filter (fun e => e.1 ∈ S)).image Prod.snd

theorem mem_nbr {E : Finset (A × B)} {S : Finset A} {b : B} :
    b ∈ nbr E S ↔ ∃ e ∈ E, e.1 ∈ S ∧ e.2 = b := by
  unfold nbr
  simp only [mem_image, mem_filter]
  constructor
  · rintro ⟨e, ⟨he, hS⟩, rfl⟩
    exact ⟨e, he, hS, rfl⟩
  · rintro ⟨e, he, hS, rfl⟩
    exact ⟨e, ⟨he, hS⟩, rfl⟩

/-- A set `S ⊆ A₀` of maximal deficiency `|S| - |N(S)|`, chosen with `|N(S)| ≤ |S|`. -/
theorem exists_max_deficiency (E : Finset (A × B)) (A0 : Finset A) :
    ∃ S ⊆ A0, (nbr E S).card ≤ S.card ∧
      ∀ S' ⊆ A0, S'.card - (nbr E S').card ≤ S.card - (nbr E S).card := by
  classical
  obtain ⟨S, hS, hmax⟩ := exists_max_image A0.powerset
    (fun S => S.card - (nbr E S).card) ⟨∅, empty_mem_powerset _⟩
  rw [mem_powerset] at hS
  by_cases h : (nbr E S).card ≤ S.card
  · exact ⟨S, hS, h, fun S' hS' => hmax S' (mem_powerset.2 hS')⟩
  · have h0 : nbr E ∅ = ∅ := by
      ext b
      simp [mem_nbr]
    refine ⟨∅, empty_subset _, le_of_eq (by rw [h0, card_empty, card_empty]), fun S' hS' => ?_⟩
    have h1 : S'.card - (nbr E S').card ≤ S.card - (nbr E S).card :=
      hmax S' (mem_powerset.2 hS')
    rw [card_empty]
    omega

/-- Kőnig's theorem from Hall's theorem (deficiency version). -/
theorem konig_proof (E : Finset (A × B)) (k : ℕ)
    (hk : ∀ M ⊆ E, Set.InjOn Prod.fst (M : Set (A × B)) →
      Set.InjOn Prod.snd (M : Set (A × B)) → M.card ≤ k) :
    ∃ KA : Finset A, ∃ KB : Finset B,
      (∀ e ∈ E, e.1 ∈ KA ∨ e.2 ∈ KB) ∧ KA.card + KB.card ≤ k := by
  classical
  set A0 := E.image Prod.fst with hA0
  obtain ⟨S, hS, hNS, hmax⟩ := exists_max_deficiency E A0
  set δ := S.card - (nbr E S).card with hδ
  -- Hall's condition in the graph augmented by `δ` dummy right vertices
  let t : A0 → Finset (B ⊕ Fin δ) := fun a => (nbr E {a.1}).disjSum (univ : Finset (Fin δ))
  have hall : ∀ s : Finset A0, s.card ≤ (s.biUnion t).card := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp
    · set S' := s.map (Function.Embedding.subtype _) with hS'
      have hS'sub : S' ⊆ A0 := by
        intro a ha
        rw [hS', mem_map] at ha
        obtain ⟨a', _, rfl⟩ := ha
        exact a'.2
      have hsub : (nbr E S').disjSum (univ : Finset (Fin δ)) ⊆ s.biUnion t := by
        intro x hx
        rw [mem_disjSum] at hx
        rw [mem_biUnion]
        rcases hx with ⟨b, hb, rfl⟩ | ⟨d, _, rfl⟩
        · rw [mem_nbr] at hb
          obtain ⟨e, he, heS, rfl⟩ := hb
          rw [hS', mem_map] at heS
          obtain ⟨a, ha, hae⟩ := heS
          have hae' : a.1 = e.1 := hae
          refine ⟨a, ha, ?_⟩
          show Sum.inl e.2 ∈ (nbr E {a.1}).disjSum (univ : Finset (Fin δ))
          rw [inl_mem_disjSum, mem_nbr]
          exact ⟨e, he, by rw [mem_singleton]; exact hae'.symm, rfl⟩
        · obtain ⟨a, ha⟩ := hne
          refine ⟨a, ha, ?_⟩
          show Sum.inr d ∈ (nbr E {a.1}).disjSum (univ : Finset (Fin δ))
          rw [inr_mem_disjSum]
          exact mem_univ _
      have h1 := card_le_card hsub
      rw [card_disjSum, card_univ, Fintype.card_fin] at h1
      have h2 : S'.card - (nbr E S').card ≤ δ := hmax S' hS'sub
      have h3 : S'.card = s.card := card_map _
      omega
  obtain ⟨f, hf, hft⟩ := (all_card_le_biUnion_card_iff_exists_injective t).1 hall
  have hft' : ∀ (a : A0) (b : B), f a = Sum.inl b → (a.1, b) ∈ E := by
    intro a b hab
    have h1 : f a ∈ (nbr E {a.1}).disjSum (univ : Finset (Fin δ)) := hft a
    rw [hab, inl_mem_disjSum, mem_nbr] at h1
    obtain ⟨e, he, he1, he2⟩ := h1
    rw [mem_singleton] at he1
    have : e = (a.1, b) := Prod.ext he1 he2
    rw [← this]
    exact he
  -- the matching extracted from `f`
  set M := E.filter (fun e => ∃ h : e.1 ∈ A0, f ⟨e.1, h⟩ = Sum.inl e.2) with hM
  have hMsub : M ⊆ E := filter_subset _ _
  have hmem : ∀ e, e ∈ M ↔ e ∈ E ∧ ∃ h : e.1 ∈ A0, f ⟨e.1, h⟩ = Sum.inl e.2 :=
    fun e => mem_filter
  have hinj1 : Set.InjOn Prod.fst (M : Set (A × B)) := by
    intro e he e' he' h
    rw [mem_coe, hmem] at he he'
    obtain ⟨_, h1, hf1⟩ := he
    obtain ⟨_, h1', hf1'⟩ := he'
    have hsub : (⟨e.1, h1⟩ : A0) = ⟨e'.1, h1'⟩ := Subtype.ext h
    have : (Sum.inl e.2 : B ⊕ Fin δ) = Sum.inl e'.2 := by
      rw [← hf1, ← hf1', hsub]
    exact Prod.ext h (Sum.inl.inj this)
  have hinj2 : Set.InjOn Prod.snd (M : Set (A × B)) := by
    intro e he e' he' h
    rw [mem_coe, hmem] at he he'
    obtain ⟨_, h1, hf1⟩ := he
    obtain ⟨_, h1', hf1'⟩ := he'
    have h2 : f ⟨e.1, h1⟩ = f ⟨e'.1, h1'⟩ := by
      rw [hf1, hf1']
      exact congrArg Sum.inl h
    have h3 := congrArg Subtype.val (hf h2)
    exact Prod.ext h3 h
  have hMk := hk M hMsub hinj1 hinj2
  -- counting: `|A₀| ≤ |M| + δ`
  have hcount : A0.card ≤ M.card + δ := by
    have hsub : (univ : Finset A0).image f ⊆
        M.image (fun e => (Sum.inl e.2 : B ⊕ Fin δ))
          ∪ (univ : Finset (Fin δ)).image (Sum.inr : Fin δ → B ⊕ Fin δ) := by
      intro x hx
      rw [mem_image] at hx
      obtain ⟨a, _, rfl⟩ := hx
      rw [mem_union]
      rcases hfa : f a with b | d
      · left
        rw [mem_image]
        refine ⟨(a.1, b), ?_, rfl⟩
        rw [hmem]
        exact ⟨hft' a b hfa, a.2, hfa⟩
      · right
        exact mem_image.2 ⟨d, mem_univ _, rfl⟩
    have h1 := card_le_card hsub
    rw [card_image_of_injective _ hf, card_univ, Fintype.card_coe] at h1
    have h2 := card_union_le (M.image (fun e => (Sum.inl e.2 : B ⊕ Fin δ)))
      ((univ : Finset (Fin δ)).image (Sum.inr : Fin δ → B ⊕ Fin δ))
    have h3 : (M.image (fun e => (Sum.inl e.2 : B ⊕ Fin δ))).card ≤ M.card := card_image_le
    have h4 : ((univ : Finset (Fin δ)).image (Sum.inr : Fin δ → B ⊕ Fin δ)).card ≤ δ := by
      refine le_trans card_image_le ?_
      rw [card_univ, Fintype.card_fin]
    omega
  -- the cover `(A₀ \ S) ∪ N(S)`
  refine ⟨A0 \ S, nbr E S, ?_, ?_⟩
  · intro e he
    by_cases h : e.1 ∈ S
    · right
      rw [mem_nbr]
      exact ⟨e, he, h, rfl⟩
    · left
      rw [mem_sdiff]
      exact ⟨mem_image_of_mem _ he, h⟩
  · rw [card_sdiff_of_subset hS]
    have := card_le_card hS
    omega

end OAI.SeymourSecondNeighborhood.Sol_OAI_SeymourSecondNeighborhood_Pruning_konig

open OAI.SeymourSecondNeighborhood in
open OAI.SeymourSecondNeighborhood.Pruning in
theorem solution {A B : Type*} (E : Finset (A × B)) (k : ℕ)
    (hk : ∀ M ⊆ E, Set.InjOn Prod.fst (M : Set (A × B)) →
      Set.InjOn Prod.snd (M : Set (A × B)) → M.card ≤ k) :
    ∃ KA : Finset A, ∃ KB : Finset B,
      (∀ e ∈ E, e.1 ∈ KA ∨ e.2 ∈ KB) ∧ KA.card + KB.card ≤ k :=
  OAI.SeymourSecondNeighborhood.Sol_OAI_SeymourSecondNeighborhood_Pruning_konig.konig_proof E k hk
