-- Prove2me | solution 1 for HyperCheeger.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T13:03:30.735542+00:00
-- url     : https://prove2.me/submissions/7eee8933-9f3e-4c88-a608-699d65be3c95

import Mathlib
import Definitions.Def_HyperCheeger_Hypergraph_diffusionConductance
import Definitions.Def_HyperCheeger_Hypergraph_aeGraph

section
set_option autoImplicit false

namespace HyperCheeger.Dev.Lemma34

open HyperCheeger HyperCheeger.Hypergraph

variable {V : Type} [DecidableEq V]

/-- Swapping the double sum over (AE pair, hyperedge containing it). -/
lemma sum_swap (H : Hypergraph V) (c : Finset V → ℝ) (P : Finset V → Prop) [DecidablePred P] :
    ∑ p ∈ (H.edges.biUnion (Finset.powersetCard 2)).filter P,
        ∑ e ∈ H.edges.filter (fun e => p ⊆ e), c e =
      ∑ e ∈ H.edges, c e * (((Finset.powersetCard 2 e).filter P).card : ℝ) := by
  rw [Finset.sum_comm' (t' := H.edges)
    (s' := fun e => (Finset.powersetCard 2 e).filter P)]
  · refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  · intro p e
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨⟨e', _, _, hp2⟩, hP⟩, he, hpe⟩
      exact ⟨⟨⟨hpe, hp2⟩, hP⟩, he⟩
    · rintro ⟨⟨⟨hpe, hp2⟩, hP⟩, he⟩
      exact ⟨⟨⟨e, he, hpe, hp2⟩, hP⟩, he, hpe⟩

/-- The pairs `{u, v} ⊆ e` crossing `T` are counted by `|e ∩ T| · |e ∩ Tᶜ|`. -/
lemma card_cross [Fintype V] (e T : Finset V) :
    ((Finset.powersetCard 2 e).filter
        (fun p => (p ∩ T).Nonempty ∧ (p ∩ Tᶜ).Nonempty)).card =
      (e ∩ T).card * (e ∩ Tᶜ).card := by
  rw [← Finset.card_product]
  symm
  refine Finset.card_bij (fun x _ => ({x.1, x.2} : Finset V)) ?_ ?_ ?_
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product, Finset.mem_inter, Finset.mem_compl] at hab
    obtain ⟨⟨hae, haT⟩, hbe, hbT⟩ := hab
    have hne : a ≠ b := fun h => hbT (h ▸ haT)
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨?_, Finset.card_pair hne⟩, ⟨a, ?_⟩, ⟨b, ?_⟩⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hae
      · rw [Finset.mem_singleton.mp hx]; exact hbe
    · simp [haT]
    · simp [hbT]
  · rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' h
    simp only [Finset.mem_product, Finset.mem_inter, Finset.mem_compl] at hab hab'
    have ha : a ∈ ({a', b'} : Finset V) := h ▸ Finset.mem_insert_self a {b}
    have hb : b ∈ ({a', b'} : Finset V) := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    have h1 : a = a' := by
      rcases ha with h | h
      · exact h
      · exact absurd (h ▸ hab.1.2) hab'.2.2
    have h2 : b = b' := by
      rcases hb with h | h
      · exact absurd (h ▸ hab'.1.2) hab.2.2
      · exact h
    rw [h1, h2]
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hp
    obtain ⟨⟨hpe, hp2⟩, ⟨x, hx⟩, ⟨y, hy⟩⟩ := hp
    rw [Finset.mem_inter] at hx hy
    rw [Finset.mem_compl] at hy
    refine ⟨(x, y), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_inter, Finset.mem_compl]
      exact ⟨⟨hpe hx.1, hx.2⟩, hpe hy.1, hy.2⟩
    · have hne : x ≠ y := fun h => hy.2 (h ▸ hx.2)
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hx.1
        · rw [Finset.mem_singleton.mp hz]; exact hy.1
      · rw [hp2, Finset.card_pair hne]

lemma aeGraph_degree [Fintype V] (H : Hypergraph V) (u : V) :
    H.aeGraph.degree u = H.degree u := by
  have hfilt : ∀ e : Finset V, (Finset.powersetCard 2 e).filter (fun p => u ∈ p) =
      (Finset.powersetCard 2 e).filter
        (fun p => (p ∩ {u}).Nonempty ∧ (p ∩ {u}ᶜ).Nonempty) := by
    intro e
    refine Finset.filter_congr fun p hp => ?_
    have hp2 := (Finset.mem_powersetCard.mp hp).2
    constructor
    · intro hu
      refine ⟨⟨u, by simp [hu]⟩, ?_⟩
      by_contra hn
      rw [Finset.not_nonempty_iff_eq_empty] at hn
      have hsub : p ⊆ {u} := by
        intro x hx
        by_contra hxu
        have : x ∈ p ∩ {u}ᶜ := by simp [hx, Finset.mem_singleton.not.mp hxu]
        rw [hn] at this; simp at this
      have := Finset.card_le_card hsub
      rw [hp2, Finset.card_singleton] at this
      omega
    · rintro ⟨⟨x, hx⟩, _⟩
      simp only [Finset.mem_inter, Finset.mem_singleton] at hx
      exact hx.2 ▸ hx.1
  have h1 : H.aeGraph.degree u =
      ∑ e ∈ H.edges, H.w e / ((e.card : ℝ) - 1) *
        (((e ∩ {u}).card * (e ∩ {u}ᶜ).card : ℕ) : ℝ) := by
    unfold Hypergraph.degree
    rw [show H.aeGraph.edges = H.edges.biUnion (Finset.powersetCard 2) from rfl]
    rw [show (fun p : Finset V => H.aeGraph.w p) =
      fun p => ∑ e ∈ H.edges with p ⊆ e, H.w e / ((e.card : ℝ) - 1) from rfl]
    rw [sum_swap]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hfilt, card_cross]
  rw [h1]
  unfold Hypergraph.degree
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun e he => ?_
  by_cases hu : u ∈ e
  · rw [if_pos hu]
    have hi : e ∩ {u} = {u} := by
      ext x; simp only [Finset.mem_inter, Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro rfl; exact ⟨hu, rfl⟩
    have hc := Finset.card_inter_add_card_sdiff e {u}
    have hsd : e \ {u} = e ∩ {u}ᶜ := by ext x; simp
    rw [hi, Finset.card_singleton, hsd] at hc
    rw [hi, Finset.card_singleton, one_mul]
    have hc' : (e.card : ℝ) - 1 = ((e ∩ {u}ᶜ).card : ℝ) := by
      rw [← hc]; push_cast; ring
    have hne : (e.card : ℝ) - 1 ≠ 0 := by
      intro h0
      have : (e.card : ℝ) = 1 := by linarith
      exact H.card_ne_one e he (by exact_mod_cast this)
    rw [← hc']
    field_simp
  · rw [if_neg hu]
    have hi : e ∩ {u} = ∅ := by
      ext x; simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
      rintro ⟨hx, rfl⟩; exact hu hx
    rw [hi]; simp

end HyperCheeger.Dev.Lemma34

namespace HyperCheeger
open HyperCheeger.Dev.Lemma34 in
theorem chk_lemma_3_4 {V : Type} [Fintype V] [DecidableEq V] (H : Hypergraph V) (T : Finset V)
    (hT : T.Nonempty) (hT' : T ≠ Finset.univ) :
    H.aeGraph.conductanceSet T = H.diffusionConductanceSet T := by
  have hvol : ∀ S : Finset V, H.aeGraph.vol S = H.vol S := fun S =>
    Finset.sum_congr rfl fun u _ => aeGraph_degree H u
  unfold Hypergraph.conductanceSet Hypergraph.diffusionConductanceSet
  rw [hvol, hvol]
  congr 1
  unfold Hypergraph.boundary
  rw [show H.aeGraph.edges = H.edges.biUnion (Finset.powersetCard 2) from rfl]
  rw [show (fun p : Finset V => H.aeGraph.w p) =
    fun p => ∑ e ∈ H.edges with p ⊆ e, H.w e / ((e.card : ℝ) - 1) from rfl]
  rw [sum_swap]
  rw [Finset.sum_filter_of_ne]
  · refine Finset.sum_congr rfl fun e _ => ?_
    rw [card_cross]; push_cast; ring
  · intro e _ hne
    constructor
    · rw [← Finset.card_pos]; refine Nat.pos_of_ne_zero fun h => hne ?_; rw [h]; simp
    · rw [← Finset.card_pos]; refine Nat.pos_of_ne_zero fun h => hne ?_; rw [h]; simp

end HyperCheeger
end

theorem solution : type_of% @HyperCheeger.chk_lemma_3_4 := @HyperCheeger.chk_lemma_3_4
