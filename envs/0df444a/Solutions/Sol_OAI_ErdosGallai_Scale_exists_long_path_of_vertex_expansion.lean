-- Prove2me | solution 1 for OAI.ErdosGallai.Scale.exists_long_path_of_vertex_expansion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T02:05:03.309567+00:00
-- url     : https://prove2.me/submissions/b8db4db8-3de3-4c9a-8d73-86682b605838

import Mathlib
import Definitions.Def_OAIQWEGC000

section
-- module Solutions.OAIQW_ErdosGallai.DepthFirstSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section

namespace ErdosGallai.Scale
universe u
open Finset SimpleGraph
variable {V : Type cycleUniverse1} [Fintype V] [DecidableEq V]

namespace DFSState
variable {G : SimpleGraph V}

lemma card_eq (s : DFSState G) :
    Fintype.card V = s.finished.card + s.stack.length + s.unexplored.card := by
  have hdis : Disjoint (s.finished ∪ s.stack.toFinset) s.unexplored :=
    Finset.disjoint_union_left.mpr ⟨s.f_u, s.s_u⟩
  have hc := congrArg Finset.card s.cover
  rw [Finset.card_union_of_disjoint hdis, Finset.card_union_of_disjoint s.f_s,
    List.toFinset_card_of_nodup s.nodup, Finset.card_univ] at hc
  exact hc.symm

lemma restart (s : DFSState G) (hs : s.stack = []) (v : V) (hv : v ∈ s.unexplored) :
    ∃ t : DFSState G, t.finished = s.finished ∧
      t.unexplored.card + 1 = s.unexplored.card := by
  have hvf : v ∉ s.finished := fun hf => Finset.disjoint_left.mp s.f_u hf hv
  refine ⟨⟨[v], s.finished, s.unexplored.erase v, by simp, by simp,
    ?_, ?_, ?_, ?_, ?_⟩, rfl, ?_⟩
  · simpa using hvf
  · exact s.f_u.mono_right (Finset.erase_subset _ _)
  · simp
  · change s.finished ∪ {v} ∪ s.unexplored.erase v = univ
    rw [Finset.union_assoc, Finset.singleton_union, Finset.insert_erase hv]
    simpa only [hs, List.toFinset_nil, Finset.union_empty] using s.cover
  · intro x hx y hy
    exact s.separation x hx y (Finset.mem_of_mem_erase hy)
  · exact Finset.card_erase_add_one hv

lemma push (s : DFSState G) (v w : V) (L : List V) (hs : s.stack = v::L)
    (hw : w ∈ s.unexplored) (hadj : G.Adj w v) :
    ∃ t : DFSState G, t.finished = s.finished ∧
      t.unexplored.card + 1 = s.unexplored.card := by
  have hws : w ∉ s.stack := fun h => Finset.disjoint_left.mp s.s_u
    (List.mem_toFinset.mpr h) hw
  have hwf : w ∉ s.finished := fun h => Finset.disjoint_left.mp s.f_u h hw
  refine ⟨⟨w::s.stack, s.finished, s.unexplored.erase w, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    rfl, ?_⟩
  · exact List.nodup_cons.mpr ⟨hws,s.nodup⟩
  · rw [hs]
    exact List.IsChain.cons_cons hadj (hs ▸ s.chain)
  · simpa using And.intro hwf s.f_s
  · exact s.f_u.mono_right (Finset.erase_subset _ _)
  · rw [List.toFinset_cons, Finset.disjoint_insert_left]
    exact ⟨(by simp), s.s_u.mono_right (Finset.erase_subset _ _)⟩
  · ext x
    have hx : x ∈ s.finished ∪ s.stack.toFinset ∪ s.unexplored := by rw [s.cover]; simp
    simp only [Finset.mem_union] at hx
    simp only [List.toFinset_cons, Finset.mem_union, Finset.mem_insert,
      Finset.mem_erase, Finset.mem_univ, iff_true]
    by_cases hxw : x = w
    · exact Or.inl (Or.inr (Or.inl hxw))
    · rcases hx with (h|h)|h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (Or.inr h))
      · exact Or.inr ⟨hxw,h⟩
  · intro x hx y hy
    exact s.separation x hx y (Finset.mem_of_mem_erase hy)
  · exact Finset.card_erase_add_one hw

lemma pop (s : DFSState G) (v : V) (L : List V) (hs : s.stack = v::L)
    (hn : ∀ w ∈ s.unexplored, ¬G.Adj v w) :
    ∃ t : DFSState G, t.finished.card = s.finished.card + 1 ∧
      t.unexplored = s.unexplored := by
  have hvf : v ∉ s.finished := fun hv => Finset.disjoint_left.mp s.f_s hv (by simp [hs])
  have hvu : v ∉ s.unexplored := fun hv => Finset.disjoint_left.mp s.s_u (by simp [hs]) hv
  have hL : L.toFinset ⊆ s.stack.toFinset := by rw [hs]; simp
  have hnd : v ∉ L ∧ L.Nodup := by simpa only [hs, List.nodup_cons] using s.nodup
  have hvL : v ∉ L := hnd.1
  refine ⟨⟨L, insert v s.finished, s.unexplored, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, rfl⟩
  · exact hnd.2
  · exact (hs ▸ s.chain).of_cons
  · exact Finset.disjoint_insert_left.mpr ⟨by simpa using hvL, s.f_s.mono_right hL⟩
  · exact Finset.disjoint_insert_left.mpr ⟨hvu,s.f_u⟩
  · exact s.s_u.mono_left hL
  · simpa [hs, Finset.insert_union] using s.cover
  · intro x hx y hy
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact hn y hy
    · exact s.separation x hx y hy
  · exact Finset.card_insert_of_notMem hvf

lemma reaches_balance (s : DFSState G) (hs : s.finished.card ≤ s.unexplored.card) :
    ∃ t : DFSState G, t.finished.card = t.unexplored.card := by
  generalize hd : s.unexplored.card - s.finished.card = d
  induction d using Nat.strong_induction_on generalizing s with
  | h d ih =>
    by_cases heq : s.finished.card = s.unexplored.card
    · exact ⟨s,heq⟩
    have hlt : s.finished.card < s.unexplored.card := lt_of_le_of_ne hs heq
    have hdpos : 0 < d := by omega
    cases hstack : s.stack with
    | nil =>
      obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0 < s.unexplored.card by omega)
      obtain ⟨t,htf,htu⟩ := s.restart hstack v hv
      apply ih (t.unexplored.card-t.finished.card) (by rw [htf]; omega) t (by rw [htf]; omega) rfl
    | cons v L =>
      by_cases hn : ∃ w ∈ s.unexplored, G.Adj v w
      · obtain ⟨w,hw,hadj⟩ := hn
        obtain ⟨t,htf,htu⟩ := s.push v w L hstack hw hadj.symm
        apply ih (t.unexplored.card-t.finished.card) (by rw [htf]; omega) t (by rw [htf]; omega) rfl
      · push Not at hn
        obtain ⟨t,htf,htu⟩ := s.pop v L hstack hn
        apply ih (t.unexplored.card-t.finished.card) (by rw [htf,htu]; omega) t (by rw [htf,htu]; omega) rfl

end DFSState

theorem exists_balanced_dfs_state (G : SimpleGraph V) :
    ∃ s : DFSState G, s.finished.card = s.unexplored.card := by
  let s : DFSState G := ⟨[], ∅, univ, by simp, by simp, by simp, by simp, by simp,
    by simp, by simp⟩
  exact s.reaches_balance (by simp [s])

end ErdosGallai.Scale

namespace ErdosGallai.Scale
open Finset SimpleGraph
variable {V : Type cycleUniverse2} [Fintype V] [DecidableEq V]

lemma DFSState.external_subset (G : SimpleGraph V) [DecidableRel G.Adj] (s : DFSState G) :
    externalNeighbors G s.unexplored ⊆ s.stack.toFinset := by
  intro v hv
  obtain ⟨_,hvu,u,hu,hadj⟩ := Finset.mem_filter.mp hv
  have hc : v ∈ s.finished ∪ s.stack.toFinset ∪ s.unexplored := by rw [s.cover]; simp
  rcases Finset.mem_union.mp hc with h|h
  · rcases Finset.mem_union.mp h with h|h
    · exact (s.separation v h u hu hadj.symm).elim
    · exact h
  · exact (hvu h).elim

theorem exists_long_path_of_vertex_expansion_oai (G : SimpleGraph V) [DecidableRel G.Adj]
    (α : ℝ) (hα : α ≤ 1)
    (hexp : ∀ U : Finset V, U.Nonempty → 2 * U.card ≤ Fintype.card V →
      α * U.card ≤ ((Finset.univ.filter (fun v => v ∉ U ∧ ∃ u ∈ U, G.Adj u v)).card : ℝ)) :
    ∃ L : List V, L.Nodup ∧ L.IsChain G.Adj ∧ α * Fintype.card V / 3 ≤ (L.length : ℝ) := by
  replace hexp : VertexExpansion G α := hexp
  obtain ⟨s,heq⟩ := exists_balanced_dfs_state G
  refine ⟨s.stack,s.nodup,s.chain,?_⟩
  have hc := s.card_eq
  rw [heq] at hc
  have hcR : (Fintype.card V : ℝ) = 2*(s.unexplored.card : ℝ)+(s.stack.length : ℝ) := by
    exact_mod_cast (show Fintype.card V = 2*s.unexplored.card+s.stack.length by omega)
  have hN : ((externalNeighbors G s.unexplored).card : ℝ) ≤ (s.stack.length : ℝ) := by
    have ht := Finset.card_le_card (s.external_subset G)
    rw [List.toFinset_card_of_nodup s.nodup] at ht
    exact_mod_cast ht
  by_cases hU : s.unexplored.Nonempty
  · have hsmall : 2*s.unexplored.card ≤ Fintype.card V := by omega
    have he := (hexp s.unexplored hU hsmall).trans hN
    have ht : (0 : ℝ) ≤ s.stack.length := Nat.cast_nonneg _
    have ha := mul_le_mul_of_nonneg_right hα ht
    nlinarith
  · have hu : s.unexplored.card = 0 := by simp [Finset.not_nonempty_iff_eq_empty.mp hU]
    rw [hu, Nat.cast_zero, mul_zero, zero_add] at hcR

    nlinarith [show (0 : ℝ) ≤ s.stack.length from Nat.cast_nonneg _,
      mul_le_mul_of_nonneg_right hα (show (0 : ℝ) ≤ s.stack.length from Nat.cast_nonneg _)]

end ErdosGallai.Scale
end
end
end

end OAI
end

theorem solution.{cycleUniverse2} : type_of% @OAI.ErdosGallai.Scale.exists_long_path_of_vertex_expansion_oai.{cycleUniverse2} := @OAI.ErdosGallai.Scale.exists_long_path_of_vertex_expansion_oai.{cycleUniverse2}
