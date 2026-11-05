-- Prove2me | solution 1 for NicerEars.TJoin.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T11:35:17.611755+00:00
-- url     : https://prove2.me/submissions/392a0843-1147-45f9-bc91-b719d2a91460

import Mathlib
import Definitions.Def_NicerEars_TJoin_Setting

open Finset NicerEars.TJoin

namespace SolProp3Aux

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem ends_rep (G : NicerEars.TJoin.Graph V E) (e : E) :
    ∃ a b, a ≠ b ∧ G.ends e = s(a, b) := by
  obtain ⟨⟨p, q⟩, hpq⟩ := Quot.exists_rep (G.ends e)
  have he : G.ends e = s(p, q) := hpq.symm
  refine ⟨p, q, ?_, he⟩
  intro h; apply G.loopless e; rw [he, h]; exact Sym2.mk_isDiag_iff.mpr rfl

/-- multiplicity vector of a multi-subgraph -/
noncomputable def mult (F : Finset (E × Fin 2)) (e : E) : ℝ :=
  (#(univ.filter (fun i : Fin 2 => (e, i) ∈ F)) : ℝ)

theorem sum_mult (F : Finset (E × Fin 2)) (S : Finset E) :
    ∑ e ∈ S, mult F e = (#(F.filter (fun p => p.1 ∈ S)) : ℝ) := by
  have h := card_eq_sum_card_fiberwise (f := Prod.fst) (s := F.filter (fun p => p.1 ∈ S))
    (t := S) (fun p hp => (mem_filter.mp hp).2)
  rw [h]
  push_cast
  apply sum_congr rfl
  intro e he
  unfold mult
  congr 1
  have : (F.filter (fun p => p.1 ∈ S)).filter (fun p => p.1 = e) =
      (univ.filter (fun i : Fin 2 => (e, i) ∈ F)).image (fun i => (e, i)) := by
    ext ⟨e', i⟩
    simp only [mem_filter, mem_image, mem_univ, true_and, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hF, -⟩, rfl⟩; exact ⟨i, hF, rfl, rfl⟩
    · rintro ⟨j, hj, rfl, rfl⟩; exact ⟨⟨hj, he⟩, rfl⟩
  rw [this, card_image_of_injective _ (fun i j h => by simpa using h)]

theorem cut_iff (G : NicerEars.TJoin.Graph V E) (W : Finset V) (e : E) (a b : V)
    (he : G.ends e = s(a, b)) :
    e ∈ G.cut W ↔ (a ∈ W ∧ b ∉ W) ∨ (b ∈ W ∧ a ∉ W) := by
  simp only [NicerEars.TJoin.Graph.cut, mem_filter, mem_univ, true_and, he, Sym2.eq_iff]
  constructor
  · rintro ⟨u, hu, v, hv, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact Or.inl ⟨hu, hv⟩
    · exact Or.inr ⟨hu, hv⟩
  · rintro (⟨ha, hb⟩ | ⟨hb, ha⟩)
    · exact ⟨a, ha, b, hb, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨b, hb, a, ha, Or.inr ⟨rfl, rfl⟩⟩

theorem claim3 (G : NicerEars.TJoin.Graph V E) (W : Finset V) (e : E) :
    ((#(W.filter (· ∈ G.ends e)) : ℕ) : ZMod 2) = if e ∈ G.cut W then 1 else 0 := by
  obtain ⟨a, b, hab, he⟩ := ends_rep G e
  have hc := cut_iff G W e a b he
  have hf : W.filter (· ∈ G.ends e) = W.filter (fun v => v = a ∨ v = b) := by
    rw [he]; simp [Sym2.mem_iff]
  rw [hf]
  by_cases ha : a ∈ W <;> by_cases hb : b ∈ W
  · have : W.filter (fun v => v = a ∨ v = b) = {a, b} := by
      ext v; simp only [mem_filter, mem_insert, mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro (rfl | rfl) <;> simp_all
    rw [this, card_pair hab, if_neg (by tauto)]; decide
  · have : W.filter (fun v => v = a ∨ v = b) = {a} := by
      ext v; simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨h1, rfl | rfl⟩
        · rfl
        · exact absurd h1 hb
      · rintro rfl; exact ⟨ha, Or.inl rfl⟩
    rw [this, if_pos (hc.mpr (Or.inl ⟨ha, hb⟩))]; simp
  · have : W.filter (fun v => v = a ∨ v = b) = {b} := by
      ext v; simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨h1, rfl | rfl⟩
        · exact absurd h1 ha
        · rfl
      · rintro rfl; exact ⟨hb, Or.inr rfl⟩
    rw [this, if_pos (hc.mpr (Or.inr ⟨hb, ha⟩))]; simp
  · have : W.filter (fun v => v = a ∨ v = b) = ∅ := by
      ext v; simp only [mem_filter, notMem_empty, iff_false, not_and]
      rintro h1 (rfl | rfl)
      · exact ha h1
      · exact hb h1
    rw [this, if_neg (by tauto)]; simp

theorem cut_even (G : NicerEars.TJoin.Graph V E) (T : Finset V) (F : Finset (E × Fin 2))
    (hF : G.double.IsTJoin T F) (W : Finset V) (hW : Even #(W ∩ T)) :
    Even #(F.filter (fun p => p.1 ∈ G.cut W)) := by
  have hdeg : ∀ v, ((#(F.filter (fun p => v ∈ G.ends p.1)) : ℕ) : ZMod 2) =
      if v ∈ T then 1 else 0 := by
    intro v
    have := hF v
    simp only [NicerEars.TJoin.Graph.double] at this
    by_cases hv : v ∈ T
    · rw [if_pos hv]; exact (ZMod.natCast_eq_one_iff_odd).mpr (this.mpr hv)
    · rw [if_neg hv]
      apply (ZMod.natCast_eq_zero_iff_even).mpr
      rcases Nat.even_or_odd (#(F.filter (fun p => v ∈ G.ends p.1))) with h | h
      · exact h
      · exact absurd (this.mp h) hv
  have h1 : (∑ v ∈ W, ((#(F.filter (fun p => v ∈ G.ends p.1)) : ℕ) : ZMod 2)) =
      ((#(W ∩ T) : ℕ) : ZMod 2) := by
    simp_rw [hdeg]
    rw [sum_boole, filter_mem_eq_inter]
  have h2 : (∑ v ∈ W, #(F.filter (fun p => v ∈ G.ends p.1))) =
      ∑ p ∈ F, #(W.filter (· ∈ G.ends p.1)) := by
    simp_rw [card_filter]
    exact sum_comm
  have h3 : (∑ p ∈ F, ((#(W.filter (· ∈ G.ends p.1)) : ℕ) : ZMod 2)) =
      ((#(F.filter (fun p => p.1 ∈ G.cut W)) : ℕ) : ZMod 2) := by
    simp_rw [claim3]
    rw [sum_boole]
  have : ((#(F.filter (fun p => p.1 ∈ G.cut W)) : ℕ) : ZMod 2) = 0 := by
    rw [← h3, ← Nat.cast_sum, ← h2, Nat.cast_sum, h1]
    exact (ZMod.natCast_eq_zero_iff_even).mpr hW
  exact (ZMod.natCast_eq_zero_iff_even).mp this

theorem cut_nonempty (G : NicerEars.TJoin.Graph V E) (F : Finset (E × Fin 2))
    (hc : (G.double.spanGraph F).Connected) (W : Finset V) (hW : W.Nonempty) (hWu : W ≠ univ) :
    (F.filter (fun p => p.1 ∈ G.cut W)).Nonempty := by
  obtain ⟨w, hw⟩ := hW
  obtain ⟨w', hw'⟩ : ∃ w', w' ∉ W := by
    by_contra h; push_neg at h; exact hWu (eq_univ_of_forall h)
  obtain ⟨p⟩ := hc.preconnected w w'
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart (W : Set V) hw hw'
  have hadj := d.adj
  simp only [NicerEars.TJoin.Graph.spanGraph, SimpleGraph.fromEdgeSet_adj] at hadj
  obtain ⟨⟨q, hq, hqe⟩, -⟩ := hadj
  refine ⟨q, mem_filter.mpr ⟨hq, ?_⟩⟩
  simp only [NicerEars.TJoin.Graph.double] at hqe
  rw [cut_iff G W q.1 _ _ hqe]
  exact Or.inl ⟨hd1, hd2⟩

theorem partition_bound (G : NicerEars.TJoin.Graph V E) (F : Finset (E × Fin 2))
    (hc : (G.double.spanGraph F).Connected) (P : Finpartition (univ : Finset V)) :
    #P.parts ≤ #(F.filter (fun p => p.1 ∈ G.crossing P)) + 1 := by
  classical
  let φ : V → P.parts := fun u => ⟨P.part u, P.part_mem.mpr (mem_univ u)⟩
  let r : P.parts → P.parts → Prop := fun A B =>
    ∃ p ∈ F, ∃ u v, G.ends p.1 = s(u, v) ∧ φ u = A ∧ φ v = B
  let Q : SimpleGraph P.parts := SimpleGraph.fromRel r
  have hφ : ∀ A : P.parts, ∃ u, φ u = A := by
    intro A
    obtain ⟨u, hu⟩ := P.nonempty_of_mem_parts A.2
    exact ⟨u, Subtype.ext (P.part_eq_of_mem A.2 hu)⟩
  have hstep : ∀ x y, (G.double.spanGraph F).Adj x y → Q.Reachable (φ x) (φ y) := by
    intro x y hxy
    simp only [NicerEars.TJoin.Graph.spanGraph, SimpleGraph.fromEdgeSet_adj] at hxy
    obtain ⟨⟨q, hq, hqe⟩, -⟩ := hxy
    by_cases h : φ x = φ y
    · rw [h]
    · apply SimpleGraph.Adj.reachable
      rw [SimpleGraph.fromRel_adj]
      exact ⟨h, Or.inl ⟨q, hq, x, y, hqe, rfl, rfl⟩⟩
  have hwalk : ∀ x y (p : (G.double.spanGraph F).Walk x y), Q.Reachable (φ x) (φ y) := by
    intro x y p
    induction p with
    | nil => rfl
    | cons h p ih => exact (hstep _ _ h).trans ih
  haveI : Nonempty V := hc.nonempty
  have hQ : Q.Connected := by
    haveI : Nonempty P.parts := ⟨φ (Classical.arbitrary V)⟩
    refine ⟨fun A B => ?_⟩
    obtain ⟨u, rfl⟩ := hφ A
    obtain ⟨w, rfl⟩ := hφ B
    obtain ⟨p⟩ := hc.preconnected u w
    exact hwalk u w p
  have hcard := hQ.card_vert_le_card_edgeSet_add_one
  let g : E × Fin 2 → Sym2 P.parts := fun p => (G.ends p.1).map φ
  have hsub : Q.edgeSet ⊆ ↑((F.filter (fun p => p.1 ∈ G.crossing P)).image g) := by
    intro z hz
    induction z using Sym2.ind with
    | h A B =>
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj] at hz
      obtain ⟨hne, hr⟩ := hz
      simp only [coe_image, coe_filter, Set.mem_image, Set.mem_setOf_eq]
      rcases hr with ⟨q, hq, u, v, hqe, rfl, rfl⟩ | ⟨q, hq, u, v, hqe, rfl, rfl⟩
      · refine ⟨q, ⟨hq, ?_⟩, ?_⟩
        · simp only [NicerEars.TJoin.Graph.crossing, mem_filter, mem_univ, true_and]
          exact ⟨u, v, hqe, fun h => hne (Subtype.ext h)⟩
        · simp [g, hqe]
      · refine ⟨q, ⟨hq, ?_⟩, ?_⟩
        · simp only [NicerEars.TJoin.Graph.crossing, mem_filter, mem_univ, true_and]
          exact ⟨u, v, hqe, fun h => hne (Subtype.ext h).symm⟩
        · simp [g, hqe, Sym2.eq_swap]
  have h1 := Nat.card_mono (Finset.finite_toSet _) hsub
  simp only [Finset.coe_sort_coe, Nat.card_eq_finsetCard] at h1
  have h2 := card_image_le (s := F.filter (fun p => p.1 ∈ G.crossing P)) (f := g)
  rw [Nat.card_eq_finsetCard] at hcard
  omega

end SolProp3Aux

open SolProp3Aux in
theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : NicerEars.TJoin.Graph V E) (hG : G.IsConnected) (T : Finset V) (hT : Even #T) :
    (∀ F : Finset (E × Fin 2), G.IsConnectedTJoin T F →
      ∃ x : E → ℝ, G.LPTFeasible T x ∧ ∑ e, x e ≤ (#F : ℝ)) ∧
    (∀ x : E → ℝ, G.LPTFeasible T x → (Fintype.card V : ℝ) - 1 ≤ ∑ e, x e) := by
  constructor
  · intro F ⟨hTJ, hc⟩
    refine ⟨mult F, ⟨fun e => by unfold mult; positivity, ?_, ?_⟩, ?_⟩
    · intro W hW hWu hWT
      rw [sum_mult]
      have he := cut_even G T F hTJ W hWT
      have hn := cut_nonempty G F hc W hW hWu
      have : 2 ≤ #(F.filter (fun p => p.1 ∈ G.cut W)) := by
        rcases he with ⟨k, hk⟩
        have := hn.card_pos
        omega
      exact_mod_cast this
    · intro P
      rw [sum_mult]
      have := partition_bound G F hc P
      have : (#P.parts : ℝ) ≤ #(F.filter (fun p => p.1 ∈ G.crossing P)) + 1 := by
        exact_mod_cast this
      linarith
    · rw [sum_mult]
      exact_mod_cast card_le_card (filter_subset _ _)
  · intro x hx
    have h := hx.2.2 ⊥
    rw [Finpartition.card_bot, card_univ] at h
    have : ∑ e ∈ G.crossing ⊥, x e ≤ ∑ e, x e :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun e _ _ => hx.1 e)
    linarith
