-- Prove2me | solution 1 for MatousekLP.Integrality.hall
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T04:03:21.820197+00:00
-- url     : https://prove2.me/submissions/933b3781-ed5b-419d-84d4-d5419756662f

import Definitions.Def_MatousekLP_Integrality_BipartiteGraph
import Mathlib

open MatousekLP.Integrality

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) (hXY : IsBipartition G X Y)
    (hN : ∀ T ⊆ X, T.card ≤ (neighborhood G Y T).card) :
    ∃ M : Finset (Sym2 V), IsMatching G M ∧ ∀ x ∈ X, ∃ e ∈ M, x ∈ e := by
  obtain ⟨hdisj, -, -⟩ := hXY
  -- Hall's condition for the family x ↦ N(x) ∩ Y, indexed by X
  set t : X → Finset V := fun x => neighborhood G Y {(x : V)}
  have hcond : ∀ s : Finset X, s.card ≤ (s.biUnion t).card := by
    intro s
    have hsub : s.map (Function.Embedding.subtype _) ⊆ X := by
      intro v hv
      obtain ⟨x, -, rfl⟩ := Finset.mem_map.mp hv
      exact x.2
    have h := hN _ hsub
    rw [Finset.card_map] at h
    refine h.trans (Finset.card_le_card ?_)
    intro w hw
    simp only [neighborhood, Finset.mem_filter, Finset.mem_map,
      Function.Embedding.coe_subtype] at hw
    obtain ⟨hwY, v, ⟨x, hx, rfl⟩, hadj⟩ := hw
    exact Finset.mem_biUnion.mpr ⟨x, hx, by simp [t, neighborhood, hwY, hadj]⟩
  obtain ⟨f, hfinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hcond
  have hfY : ∀ x : X, f x ∈ Y ∧ G.Adj x (f x) := by
    intro x
    have := hf x
    simpa [t, neighborhood] using this
  refine ⟨Finset.univ.image fun x : X => s((x : V), f x), ⟨?_, ?_⟩, ?_⟩
  · intro e he
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp he
    exact (hfY x).2
  · intro v
    rw [Finset.card_le_one]
    intro e he e' he'
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at he he'
    obtain ⟨⟨x, rfl⟩, hvx⟩ := he
    obtain ⟨⟨x', rfl⟩, hvx'⟩ := he'
    have hXY' : ∀ {a}, a ∈ X → a ∉ Y := fun ha hb => Finset.disjoint_left.mp hdisj ha hb
    rcases Sym2.mem_iff.mp hvx with h1 | h1 <;> rcases Sym2.mem_iff.mp hvx' with h2 | h2
    · have : x = x' := Subtype.ext (h1.symm.trans h2)
      rw [this]
    · exact absurd (h2 ▸ (hfY x').1) (hXY' (h1 ▸ x.2))
    · exact absurd (h1 ▸ (hfY x).1) (hXY' (h2 ▸ x'.2))
    · have : x = x' := hfinj (h1.symm.trans h2)
      rw [this]
  · intro x hx
    exact ⟨s(x, f ⟨x, hx⟩), Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩, Sym2.mem_mk_left _ _⟩
