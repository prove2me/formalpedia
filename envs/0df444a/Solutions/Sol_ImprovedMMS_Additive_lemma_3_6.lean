-- Prove2me | solution 1 for ImprovedMMS.Additive.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:05:54.515858+00:00
-- url     : https://prove2.me/submissions/de515e0c-15a2-4a86-99c6-5baeeacb7b5f

import Mathlib
import Definitions.Def_ImprovedMMS_Additive_Bipartite

set_option autoImplicit false
open ImprovedMMS.Additive

theorem solution {α β : Type*} [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (E : Finset (α × β)) (hE : E ⊆ X ×ˢ Y)
    (Mt : Finset (α × β)) (hM : IsMaxMatching E Mt) :
    ∀ T ⊆ X \ FH E Mt X Y, T.Nonempty → T.card < (nbhd E T).card := by
  intro T hT hTne
  obtain ⟨hMsub, hM1, hM2⟩ := hM.1
  -- the set of mates of T
  set MT : Finset β := (Mt.filter (fun e => e.1 ∈ T)).image Prod.snd with hMT
  have hmemMT : ∀ y, y ∈ MT ↔ ∃ x ∈ T, (x, y) ∈ Mt := by
    intro y
    simp only [hMT, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨e, ⟨he, hx⟩, rfl⟩
      exact ⟨e.1, hx, he⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨(x, y), ⟨hxy, hx⟩, rfl⟩
  -- every vertex of T is matched to a reachable vertex
  have hmatched : ∀ x ∈ T, ∃ y, AltReach E Mt Y y ∧ (x, y) ∈ Mt := by
    intro x hx
    have := hT hx
    rw [Finset.mem_sdiff] at this
    obtain ⟨hxX, hxF⟩ := this
    classical
    simp only [FH, Finset.mem_filter] at hxF
    by_contra hcon
    exact hxF ⟨hxX, hcon⟩
  -- |MT| = |T|
  have hcard : MT.card = T.card := by
    have h1 : (Mt.filter (fun e => e.1 ∈ T)).card = T.card := by
      refine Finset.card_bij (fun e _ => e.1) ?_ ?_ ?_
      · intro e he
        exact (Finset.mem_filter.mp he).2
      · intro e he e' he' h
        exact hM1 e (Finset.mem_filter.mp he).1 e' (Finset.mem_filter.mp he').1 h
      · intro x hx
        obtain ⟨y, _, hy⟩ := hmatched x hx
        exact ⟨(x, y), Finset.mem_filter.mpr ⟨hy, hx⟩, rfl⟩
    rw [hMT, Finset.card_image_of_injOn, h1]
    intro e he e' he' h
    exact hM2 e (Finset.mem_filter.mp he).1 e' (Finset.mem_filter.mp he').1 h
  have hsub : MT ⊆ nbhd E T := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := (hmemMT y).mp hy
    unfold nbhd
    rw [Finset.mem_image]
    exact ⟨(x, y), Finset.mem_filter.mpr ⟨hMsub hxy, hx⟩, rfl⟩
  -- key: an extra neighbour
  have key : ∀ y, AltReach E Mt Y y → ∀ x, (x, y) ∈ Mt → x ∈ T → ∃ y'' ∈ nbhd E T, y'' ∉ MT := by
    intro y hy
    induction hy with
    | unsat hyY hyun =>
      intro x hx _
      exact absurd hx (hyun x)
    | @step y y' x hy0 hxy hxyM hxy' ih =>
      intro x'' hx'' hxT
      have hxx : x'' = x := by
        have := hM2 _ hx'' _ hxy' rfl
        exact (Prod.mk.inj this).1
      subst hxx
      have hynb : y ∈ nbhd E T := by
        unfold nbhd
        rw [Finset.mem_image]
        exact ⟨(x'', y), Finset.mem_filter.mpr ⟨hxy, hxT⟩, rfl⟩
      by_cases hmate : ∃ x₀, (x₀, y) ∈ Mt
      · obtain ⟨x₀, hx₀⟩ := hmate
        by_cases hx₀T : x₀ ∈ T
        · exact ih x₀ hx₀ hx₀T
        · refine ⟨y, hynb, fun hyMT => ?_⟩
          obtain ⟨x₁, hx₁, hx₁y⟩ := (hmemMT y).mp hyMT
          have := hM2 _ hx₁y _ hx₀ rfl
          exact hx₀T ((Prod.mk.inj this).1 ▸ hx₁)
      · refine ⟨y, hynb, fun hyMT => ?_⟩
        obtain ⟨x₁, _, hx₁y⟩ := (hmemMT y).mp hyMT
        exact hmate ⟨x₁, hx₁y⟩
  obtain ⟨x₀, hx₀⟩ := hTne
  obtain ⟨y₀, hy₀r, hy₀⟩ := hmatched x₀ hx₀
  obtain ⟨y'', hy''nb, hy''MT⟩ := key y₀ hy₀r x₀ hy₀ hx₀
  rw [← hcard]
  exact Finset.card_lt_card ⟨hsub, fun hh => hy''MT (hh hy''nb)⟩
