-- Prove2me | solution 1 for LefebvreVariations.ryser_three_intersecting
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T22:24:10.201302+00:00
-- url     : https://prove2.me/submissions/0717b907-606d-47dd-9248-72ce8d42e0b2

import Mathlib
import Definitions.Def_TenChallenges_Hypergraph

set_option autoImplicit false

open FinHypergraph

/-- Combinatorial core: a family of triples (coordinates `p 0`, `p 1`, `p 2`) in which
any two agree in some coordinate is covered by two (coordinate, value) pairs. -/
private lemma key {ι W : Type*} (p : Fin 3 → ι → W)
    (hint : ∀ s t : ι, ∃ i, p i s = p i t) (e0 : ι) :
    ∃ (i j : Fin 3) (s t : ι), ∀ k, p i k = p i s ∨ p j k = p j t := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h, h1, h2⟩ := hcon 1 2 e0 e0
  obtain ⟨g, g0, g2⟩ := hcon 0 2 e0 e0
  obtain ⟨f, f0, f1⟩ := hcon 0 1 e0 e0
  obtain ⟨k, k0, k0'⟩ := hcon 0 0 e0 f
  have he := hint h e0
  have ge := hint g e0
  have fe := hint f e0
  have fg := hint f g
  have fh := hint f h
  have gh := hint g h
  have ke := hint k e0
  have kf := hint k f
  have kg := hint k g
  have kh := hint k h
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero] at he ge fe fg fh gh ke kf kg kh
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at *
  grind

theorem solution {V : Type*} [DecidableEq V] (H : FinHypergraph V)
    (hu : H.IsUniform 3) (hp : H.IsPartite 3)
    (hint : ∀ e ∈ H.edges, ∀ f ∈ H.edges, (e ∩ f).Nonempty) :
    H.coverNumber ≤ 2 := by
  obtain ⟨parts, hv, -, hpart⟩ := hp
  by_cases hE : ∃ e0, e0 ∈ H.edges
  · obtain ⟨e0, he0⟩ := hE
    -- `p i e` is the unique vertex of the edge `e` in part `i`.
    let p : Fin 3 → H.edges → V := fun i e =>
      Classical.choose (Finset.card_eq_one.mp (hpart e.1 e.2 i))
    have hp : ∀ i (e : H.edges), parts i ∩ e.1 = {p i e} := fun i e =>
      Classical.choose_spec (Finset.card_eq_one.mp (hpart e.1 e.2 i))
    have hmem : ∀ i (e : H.edges), p i e ∈ e.1 := fun i e => by
      have : p i e ∈ parts i ∩ e.1 := by rw [hp]; exact Finset.mem_singleton_self _
      exact (Finset.mem_inter.mp this).2
    have huniq : ∀ i (e : H.edges) v, v ∈ parts i → v ∈ e.1 → v = p i e := by
      intro i e v hvi hve
      have : v ∈ parts i ∩ e.1 := Finset.mem_inter.mpr ⟨hvi, hve⟩
      rw [hp] at this
      exact Finset.mem_singleton.mp this
    have hint' : ∀ s t : H.edges, ∃ i, p i s = p i t := by
      intro s t
      obtain ⟨v, hvst⟩ := hint s.1 s.2 t.1 t.2
      obtain ⟨hvs, hvt⟩ := Finset.mem_inter.mp hvst
      obtain ⟨i, hi⟩ := (hv v).mp (H.edges_subset_vertices _ s.2 hvs)
      exact ⟨i, (huniq i s v hi hvs).symm.trans (huniq i t v hi hvt)⟩
    obtain ⟨i, j, s, t, hcov⟩ := key p hint' ⟨e0, he0⟩
    refine le_trans (Nat.sInf_le ⟨{p i s, p j t}, ⟨?_, ?_⟩, rfl⟩) Finset.card_le_two
    · intro v hv'
      rcases Finset.mem_insert.mp hv' with rfl | hv'
      · exact H.edges_subset_vertices _ s.2 (hmem i s)
      · rw [Finset.mem_singleton.mp hv']
        exact H.edges_subset_vertices _ t.2 (hmem j t)
    · intro e he
      rcases hcov ⟨e, he⟩ with h | h
      · exact ⟨p i s, Finset.mem_insert_self _ _, h ▸ hmem i ⟨e, he⟩⟩
      · exact ⟨p j t, Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
          h ▸ hmem j ⟨e, he⟩⟩
  · push Not at hE
    refine le_trans (Nat.sInf_le ⟨∅, ⟨Finset.empty_subset _, ?_⟩, rfl⟩) (by simp)
    intro e he
    exact absurd he (hE e)
