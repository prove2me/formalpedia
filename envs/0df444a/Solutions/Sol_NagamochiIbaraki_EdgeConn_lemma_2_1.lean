-- Prove2me | solution 1 for NagamochiIbaraki.EdgeConn.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:30:14.144729+00:00
-- url     : https://prove2.me/submissions/d80be8e5-c5f7-447b-beae-26b81768b44f

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NagamochiIbaraki_EdgeConn_localEdgeConn

namespace NagamochiIbaraki.EdgeConn

theorem aux_ni21_closed {V : Type*} (G : SimpleGraph V) (S : Set V)
    (hS : ∀ u v, G.Adj u v → u ∈ S → v ∈ S) {x y : V} (h : G.Reachable x y) (hx : x ∈ S) :
    y ∈ S := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hx
  | cons had _ ih => exact ih (hS _ _ had hx)

theorem aux_ni21_adj {V E : Type*} (ends : E → Sym2 V) (F : Finset E) (u v : V) :
    (edgeGraph ends F).Adj u v ↔ (∃ e ∈ F, ends e = s(u, v)) ∧ u ≠ v := by
  unfold edgeGraph
  rw [SimpleGraph.fromEdgeSet_adj]
  simp

theorem aux_ni21_edge {V E : Type*} (ends : E → Sym2 V) (F : Finset E) {f : E} (hf : f ∈ F)
    {u v : V} (h : ends f = s(u, v)) : (edgeGraph ends F).Reachable u v := by
  by_cases huv : u = v
  · subst huv; rfl
  · exact SimpleGraph.Adj.reachable ((aux_ni21_adj ends F u v).2 ⟨⟨f, hf, h⟩, huv⟩)

theorem aux_ni21_mono {V E : Type*} (ends : E → Sym2 V) {F F' : Finset E} (h : F ⊆ F')
    {u v : V} (hr : (edgeGraph ends F).Reachable u v) : (edgeGraph ends F').Reachable u v := by
  refine SimpleGraph.Reachable.mono ?_ hr
  intro a b hab
  rw [aux_ni21_adj] at hab ⊢
  obtain ⟨⟨e, he, hee⟩, hne⟩ := hab
  exact ⟨⟨e, h he, hee⟩, hne⟩

theorem aux_ni21_split {V E : Type*} [DecidableEq E] (ends : E → Sym2 V) (F : Finset E) (e : E)
    {a b : V} (hab : ends e = s(a, b)) {u v : V}
    (h : (edgeGraph ends (insert e F)).Reachable u v) :
    (edgeGraph ends F).Reachable u v ∨
      ((edgeGraph ends F).Reachable u a ∧ (edgeGraph ends F).Reachable b v) ∨
      ((edgeGraph ends F).Reachable u b ∧ (edgeGraph ends F).Reachable a v) := by
  refine aux_ni21_closed _ {w | (edgeGraph ends F).Reachable u w ∨
      ((edgeGraph ends F).Reachable u a ∧ (edgeGraph ends F).Reachable b w) ∨
      ((edgeGraph ends F).Reachable u b ∧ (edgeGraph ends F).Reachable a w)} ?_ h
      (Or.inl (SimpleGraph.Reachable.refl u))
  intro p q hpq hp
  rw [aux_ni21_adj] at hpq
  obtain ⟨⟨f, hf, hfe⟩, _⟩ := hpq
  simp only [Set.mem_setOf_eq] at hp ⊢
  rcases Finset.mem_insert.1 hf with hfe' | hf'
  · rw [hfe', hab, Sym2.eq_iff] at hfe
    have ra : (edgeGraph ends F).Reachable a a := SimpleGraph.Reachable.refl a
    have rb : (edgeGraph ends F).Reachable b b := SimpleGraph.Reachable.refl b
    rcases hfe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · tauto
    · tauto
  · have hpq' : (edgeGraph ends F).Reachable p q := aux_ni21_edge ends F hf' hfe
    rcases hp with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (h1.trans hpq')
    · exact Or.inr (Or.inl ⟨h1, h2.trans hpq'⟩)
    · exact Or.inr (Or.inr ⟨h1, h2.trans hpq'⟩)

theorem aux_ni21_forest {V E : Type*} [DecidableEq E] (ends : E → Sym2 V) (F : Finset E) (e : E)
    (hF : IsForest ends F) (he : e ∉ F) (hnot : ¬ IsForest ends (insert e F))
    {a b : V} (hab : ends e = s(a, b)) : (edgeGraph ends F).Reachable a b := by
  by_contra hr
  apply hnot
  intro f hf u v hfuv hreach
  rcases Finset.mem_insert.1 hf with hfe | hf'
  · subst hfe
    rw [Finset.erase_insert he] at hreach
    rw [hab, Sym2.eq_iff] at hfuv
    rcases hfuv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hr hreach
    · exact hr hreach.symm
  · have hfe : e ≠ f := by rintro rfl; exact he hf'
    rw [Finset.erase_insert_of_ne hfe] at hreach
    have huv : (edgeGraph ends F).Reachable u v := aux_ni21_edge ends F hf' hfuv
    rcases aux_ni21_split ends (F.erase f) e hab hreach with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hF f hf' u v hfuv h1
    · exact hr ((aux_ni21_mono ends (Finset.erase_subset f F) h1).symm.trans
        (huv.trans (aux_ni21_mono ends (Finset.erase_subset f F) h2).symm))
    · exact hr ((aux_ni21_mono ends (Finset.erase_subset f F) h2).trans
        (huv.symm.trans (aux_ni21_mono ends (Finset.erase_subset f F) h1)))

end NagamochiIbaraki.EdgeConn

open NagamochiIbaraki.EdgeConn

theorem solution
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hV : 2 ≤ Fintype.card V)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (F : ℕ → Finset E)
    (hF : ∀ i : ℕ, 1 ≤ i → i ≤ Fintype.card E →
      IsMaxSpanningForest ends (Finset.univ \ (Finset.Icc 1 (i - 1)).biUnion F) (F i)) :
    ∀ i : ℕ, 1 ≤ i → i ≤ Fintype.card E → ∀ x y : V,
      min (localEdgeConn ends Finset.univ x y) (i : ℕ∞) ≤
        localEdgeConn ends ((Finset.Icc 1 i).biUnion F) x y := by
  intro i hi1 hiE x y
  unfold localEdgeConn
  refine le_iInf₂ ?_
  intro W hW
  simp only [Set.mem_setOf_eq] at hW
  obtain ⟨_, hWr⟩ := hW
  by_cases hcard : (i : ℕ∞) ≤ W.card
  · exact (min_le_right _ _).trans hcard
  · push_neg at hcard
    have hlt : W.card < i := by exact_mod_cast hcard
    have hdisj : ∀ j ∈ Finset.Icc 1 i, ∀ k ∈ Finset.Icc 1 i, j ≠ k → Disjoint (F j) (F k) := by
      have key : ∀ j k, 1 ≤ j → j < k → k ≤ i → Disjoint (F j) (F k) := by
        intro j k hj hjk hki
        have hsub := (hF k (by omega) (by omega)).1
        rw [Finset.disjoint_left]
        intro e hej hek
        have := hsub hek
        rw [Finset.mem_sdiff] at this
        apply this.2
        exact Finset.mem_biUnion.2 ⟨j, Finset.mem_Icc.2 ⟨hj, by omega⟩, hej⟩
      intro j hj k hk hjk
      rw [Finset.mem_Icc] at hj hk
      rcases lt_or_gt_of_ne hjk with h | h
      · exact key j k hj.1 h hk.2
      · exact (key k j hk.1 h hj.2).symm
    obtain ⟨j, hj, hjW⟩ : ∃ j ∈ Finset.Icc 1 i, Disjoint (F j) W := by
      by_contra hne
      push_neg at hne
      have h1 : ((Finset.Icc 1 i).biUnion (fun j => F j ∩ W)).card ≤ W.card :=
        Finset.card_le_card (Finset.biUnion_subset.2 (fun j _ => Finset.inter_subset_right))
      have h2 : ((Finset.Icc 1 i).biUnion (fun j => F j ∩ W)).card =
          ∑ j ∈ Finset.Icc 1 i, (F j ∩ W).card := by
        rw [Finset.card_biUnion]
        intro j hj k hk hjk
        exact Finset.disjoint_of_subset_left Finset.inter_subset_left
          (Finset.disjoint_of_subset_right Finset.inter_subset_left (hdisj j hj k hk hjk))
      have h3 : ∑ j ∈ Finset.Icc 1 i, 1 ≤ ∑ j ∈ Finset.Icc 1 i, (F j ∩ W).card := by
        apply Finset.sum_le_sum
        intro j hj
        exact Finset.card_pos.2 (Finset.not_disjoint_iff_nonempty_inter.1 (hne j hj))
      simp only [Finset.sum_const, Nat.card_Icc, smul_eq_mul, mul_one] at h3
      omega
    have hj' := Finset.mem_Icc.1 hj
    obtain ⟨_, hFfor, hFmax⟩ := hF j hj'.1 (by omega)
    have hFjGi : F j ⊆ (Finset.Icc 1 i).biUnion F := fun f hf => Finset.mem_biUnion.2 ⟨j, hj, hf⟩
    have hsub2 : F j ⊆ (Finset.Icc 1 i).biUnion F \ W := by
      intro f hf
      rw [Finset.mem_sdiff]
      exact ⟨hFjGi hf, Finset.disjoint_left.1 hjW hf⟩
    have hclosed : ∀ u v, (edgeGraph ends (Finset.univ \ W)).Adj u v →
        u ∈ {w | (edgeGraph ends ((Finset.Icc 1 i).biUnion F \ W)).Reachable x w} →
        v ∈ {w | (edgeGraph ends ((Finset.Icc 1 i).biUnion F \ W)).Reachable x w} := by
      intro u v huv hu
      rw [aux_ni21_adj] at huv
      obtain ⟨⟨e, he, heuv⟩, _⟩ := huv
      have heW : e ∉ W := (Finset.mem_sdiff.1 he).2
      simp only [Set.mem_setOf_eq] at hu ⊢
      by_cases heG : e ∈ (Finset.Icc 1 i).biUnion F
      · exact hu.trans (aux_ni21_edge ends _ (Finset.mem_sdiff.2 ⟨heG, heW⟩) heuv)
      · have heH : e ∈ Finset.univ \ (Finset.Icc 1 (j - 1)).biUnion F := by
          rw [Finset.mem_sdiff]
          refine ⟨Finset.mem_univ e, ?_⟩
          intro h
          apply heG
          obtain ⟨k, hk, hek⟩ := Finset.mem_biUnion.1 h
          rw [Finset.mem_Icc] at hk
          exact Finset.mem_biUnion.2 ⟨k, Finset.mem_Icc.2 ⟨hk.1, by omega⟩, hek⟩
        have heF : e ∉ F j := fun h => heG (hFjGi h)
        have hr := aux_ni21_forest ends (F j) e hFfor heF (hFmax e heH heF) heuv
        exact hu.trans (aux_ni21_mono ends hsub2 hr)
    have hnr : ¬ (edgeGraph ends (Finset.univ \ W)).Reachable x y := fun h =>
      hWr (aux_ni21_closed _ _ hclosed h (SimpleGraph.Reachable.refl x))
    exact (min_le_left _ _).trans (iInf₂_le W ⟨Finset.subset_univ W, hnr⟩)
