-- Prove2me | solution 1 for Menger27.Graphs.grad_ge
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T05:56:20.177119+00:00
-- url     : https://prove2.me/submissions/252a2b09-f94a-458d-8b18-002451d39ceb

import Mathlib
import Definitions.Def_Menger27_Graphs_Separation



namespace Menger27.Graphs

theorem sep_of_choice {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (P Q : Finset V) (hPQ : Disjoint P Q) (f : Sym2 V → V) (hf : ∀ e ∈ G.edgeSet, f e ∈ e) :
    Separates G P Q (G.edgeFinset.image f) := by
  intro x hx y hy w
  cases w with
  | nil => exact absurd hy (Finset.disjoint_left.mp hPQ hx)
  | @cons _ v _ h p =>
    have he : s(x, v) ∈ G.edgeFinset := by simpa using h
    have hm := hf s(x, v) (by simpa using h)
    refine ⟨f s(x, v), ?_, Finset.mem_image_of_mem f he⟩
    rcases Sym2.mem_iff.mp hm with h1 | h1
    · rw [h1]; simp
    · rw [h1]; simp

theorem grad_ge_core {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ)
    (hG : NPointConnected G P Q n) :
    n ≤ G.edgeFinset.card := by
  classical
  have := hG _ (sep_of_choice G P Q hPQ (fun e : Sym2 V => e.out.1) (fun e _ => Sym2.out_fst_mem e))
  exact this.trans Finset.card_image_le

theorem grad_eq_consists_core {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ)
    (hG : NPointConnected G P Q n) (hgrad : G.edgeFinset.card = n) :
    ∃ (a b : Fin n → V) (w : ∀ i, G.Walk (a i) (b i)),
      (∀ i, a i ∈ P ∧ b i ∈ Q ∧ (w i).IsPath) ∧
      (∀ i j, i ≠ j → List.Disjoint (w i).support (w j).support) ∧
      ∀ e ∈ G.edgeSet, ∃ i, e ∈ (w i).edges := by
  classical
  -- injectivity of any choice function
  have hinj : ∀ f : Sym2 V → V, (∀ e ∈ G.edgeSet, f e ∈ e) → Set.InjOn f (G.edgeFinset : Set (Sym2 V)) := by
    intro f hf
    have h1 := hG _ (sep_of_choice G P Q hPQ f hf)
    have h2 : (G.edgeFinset.image f).card = G.edgeFinset.card := le_antisymm Finset.card_image_le (hgrad ▸ h1)
    exact Finset.card_image_iff.mp h2
  -- matching
  have hmatch : ∀ e1 ∈ G.edgeFinset, ∀ e2 ∈ G.edgeFinset, ∀ v, v ∈ e1 → v ∈ e2 → e1 = e2 := by
    intro e1 h1 e2 h2 v hv1 hv2
    by_contra hne
    let f : Sym2 V → V := fun e => if e = e1 ∨ e = e2 then v else e.out.1
    have hf : ∀ e ∈ G.edgeSet, f e ∈ e := by
      intro e _
      by_cases hc : e = e1 ∨ e = e2
      · simp only [f, if_pos hc]; rcases hc with rfl | rfl <;> assumption
      · simp only [f, if_neg hc]; exact Sym2.out_fst_mem e
    have := hinj f hf h1 h2 (by simp [f, hne])
    exact hne this
  -- every edge joins P and Q
  have hPQe : ∀ e ∈ G.edgeFinset, ∃ x y, e = s(x, y) ∧ x ∈ P ∧ y ∈ Q := by
    intro e he
    let f : Sym2 V → V := fun e => e.out.1
    have hf : ∀ e ∈ G.edgeSet, f e ∈ e := fun e _ => Sym2.out_fst_mem e
    have hS := sep_of_choice G P Q hPQ f hf
    have hcard : (G.edgeFinset.image f).card = n := le_antisymm (Finset.card_image_le.trans hgrad.le) (hG _ hS)
    have hns : ¬ Separates G P Q ((G.edgeFinset.image f).erase (f e)) := by
      intro h
      have := hG _ h
      rw [Finset.card_erase_of_mem (Finset.mem_image_of_mem f he), hcard] at this
      have : 0 < n := by rw [← hcard]; exact Finset.card_pos.mpr ⟨_, Finset.mem_image_of_mem f he⟩
      omega
    unfold Separates at hns
    push_neg at hns
    obtain ⟨x, hx, y, hy, w, hw⟩ := hns
    -- first edge of any such walk is e
    have key : ∀ {x y : V} (w : G.Walk x y), x ≠ y →
        (∀ v ∈ w.support, v ∉ (G.edgeFinset.image f).erase (f e)) → ∃ v, e = s(x, v) := by
      intro x y w hxy hw
      cases w with
      | nil => exact absurd rfl hxy
      | @cons _ v _ h p =>
        have he' : s(x, v) ∈ G.edgeFinset := by simpa using h
        have hm := hf s(x, v) (by simpa using h)
        have hsup : f s(x, v) ∈ (SimpleGraph.Walk.cons h p).support := by
          rcases Sym2.mem_iff.mp hm with h1 | h1
          · rw [h1]; simp
          · rw [h1]; simp
        have := hw _ hsup
        have hmem : f s(x, v) ∈ G.edgeFinset.image f := Finset.mem_image_of_mem f he'
        have heq : f s(x, v) = f e := by
          by_contra hne; exact this (Finset.mem_erase.mpr ⟨hne, hmem⟩)
        exact ⟨v, (hinj f hf he he' heq.symm)⟩
    have hxy : x ≠ y := fun h => Finset.disjoint_left.mp hPQ hx (h ▸ hy)
    obtain ⟨v, hv⟩ := key w hxy hw
    obtain ⟨v', hv'⟩ := key w.reverse hxy.symm (by simpa using hw)
    have hye : y ∈ e := by rw [hv']; simp
    rw [hv] at hye
    rcases Sym2.mem_iff.mp hye with h | h
    · exact absurd h.symm hxy
    · exact ⟨x, y, by rw [hv, h], hx, hy⟩
  let ε : Fin n ≃ G.edgeFinset := (Finset.equivFinOfCardEq hgrad).symm
  have hc : ∀ i, ∃ x y, (ε i : Sym2 V) = s(x, y) ∧ x ∈ P ∧ y ∈ Q := fun i => hPQe _ (ε i).2
  choose a b hab haP hbQ using hc
  have hadj : ∀ i, G.Adj (a i) (b i) := by
    intro i
    have := (ε i).2
    rw [hab i] at this
    simpa using this
  refine ⟨a, b, fun i => (hadj i).toWalk, ?_, ?_, ?_⟩
  · intro i
    refine ⟨haP i, hbQ i, ?_⟩
    simp [SimpleGraph.Walk.isPath_def, (hadj i).ne]
  · intro i j hij v hv1 hv2
    simp at hv1 hv2
    have h1 : v ∈ (ε i : Sym2 V) := by rw [hab i]; rcases hv1 with rfl | rfl <;> simp
    have h2 : v ∈ (ε j : Sym2 V) := by rw [hab j]; rcases hv2 with rfl | rfl <;> simp
    exact hij (ε.injective (Subtype.ext (hmatch _ (ε i).2 _ (ε j).2 v h1 h2)))
  · intro e he
    have he' : e ∈ G.edgeFinset := by simpa using he
    obtain ⟨i, hi⟩ := ε.surjective ⟨e, he'⟩
    refine ⟨i, ?_⟩
    have : e = s(a i, b i) := by rw [← hab i, hi]
    simp [this]

end Menger27.Graphs

open Menger27.Graphs


theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ)
    (hG : NPointConnected G P Q n) :
    n ≤ G.edgeFinset.card := by
  exact grad_ge_core G P Q hPQ n hG
