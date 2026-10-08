-- Prove2me | solution 1 for GilmoreGomoryTSP.MinCost.lemma_7_graphStar_connected
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:38:57.152555+00:00
-- url     : https://prove2.me/submissions/0c84920b-2d6b-48e7-bd40-36424a96c697

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model
import Definitions.Def_GilmoreGomoryTSP_MinCost_Underestimate



namespace GilmoreGomoryTSP.MinCost

variable {n : ℕ}

lemma l7_adj (φ ψ : Equiv.Perm (Fin (n + 1))) (q : Fin n) (hq : q ∈ starArcs φ ψ) :
    (graphStar φ ψ).Adj q.castSucc q.succ := by
  have hne : q.castSucc ≠ q.succ := (Fin.castSucc_lt_succ).ne
  refine (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inr ?_)
  simp only [SimpleGraph.fromRel_adj]
  refine ⟨hne, Or.inl ?_⟩
  simp only [adjArcs, Finset.mem_image]
  exact ⟨q, hq, rfl⟩

lemma l7_interval (φ ψ : Equiv.Perm (Fin (n + 1))) :
    ∀ (k : ℕ) (a b : Fin (n + 1)), b.val = a.val + k →
      (∀ q : Fin n, a ≤ q.castSucc → q.castSucc < b → q ∈ starArcs φ ψ) →
      (graphStar φ ψ).Reachable a b := by
  intro k
  induction k with
  | zero =>
    intro a b hab _
    have : a = b := Fin.ext (by omega)
    subst this; exact SimpleGraph.Reachable.refl _
  | succ k ih =>
    intro a b hab hq
    have han : a.val < n := by have := b.isLt; omega
    let c : Fin n := ⟨a.val, han⟩
    have hc1 : c.castSucc = a := Fin.ext rfl
    have hc2 : c.succ.val = a.val + 1 := rfl
    have h1 : (graphStar φ ψ).Reachable a c.succ := by
      have := l7_adj φ ψ c (hq c (by rw [hc1]) (by
        rw [Fin.lt_def]; show a.val < b.val; omega))
      rw [hc1] at this
      exact this.reachable
    refine h1.trans (ih c.succ b (by omega) ?_)
    intro q h1q h2q
    have h3 : c.succ.val ≤ q.castSucc.val := h1q
    have h4 : a.val ≤ q.castSucc.val := by omega
    exact hq q h4 h2q

lemma l7_core (φ ψ : Equiv.Perm (Fin (n + 1))) (hψ : IsTour ψ) :
    (graphStar φ ψ).Connected := by
  classical
  have hstep : ∀ x : Fin (n+1), (graphStar φ ψ).Reachable x (φ.symm (ψ x)) := by
    intro x
    rcases le_total x (φ.symm (ψ x)) with h | h
    · refine l7_interval φ ψ ((φ.symm (ψ x)).val - x.val) x _ (by
        have := Fin.le_def.mp h; omega) ?_
      intro q h1 h2
      simp only [starArcs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inl ⟨x, h1, h2⟩
    · refine (l7_interval φ ψ (x.val - (φ.symm (ψ x)).val) (φ.symm (ψ x)) x (by
        have := Fin.le_def.mp h; omega) ?_).symm
      intro q h1 h2
      simp only [starArcs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inr ⟨x, h1, h2⟩
  have hφ : ∀ x : Fin (n+1), (graphStar φ ψ).Reachable x (φ x) := by
    intro x
    by_cases h : φ x = x
    · rw [h]
    · apply SimpleGraph.Adj.reachable
      refine (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inl ?_)
      simp only [graph, SimpleGraph.fromRel_adj]
      exact ⟨fun h' => h h'.symm, by simp⟩
  have hψx : ∀ x : Fin (n+1), (graphStar φ ψ).Reachable x (ψ x) := by
    intro x
    have h1 := hstep x
    have h2 := hφ (φ.symm (ψ x))
    simp only [Equiv.apply_symm_apply] at h2
    exact h1.trans h2
  let x0 : Fin (n+1) := 0
  let s : Finset (Fin (n+1)) := Finset.univ.filter fun y => (graphStar φ ψ).Reachable x0 y
  have hsub : s.map ψ.toEmbedding ⊆ s := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hz
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact hy.trans (hψx y)
  have heq : s.map ψ.toEmbedding = s :=
    Finset.eq_of_subset_of_card_le hsub (by simp)
  have hall : s = Finset.univ := by
    by_contra hne
    exact hψ s ⟨x0, by simp [s]⟩ hne heq
  have hreach : ∀ y, (graphStar φ ψ).Reachable x0 y := by
    intro y
    have : y ∈ s := by rw [hall]; exact Finset.mem_univ _
    simpa [s] using this
  refine ⟨fun u v => ?_⟩
  exact (hreach u).symm.trans (hreach v)

end GilmoreGomoryTSP.MinCost

open GilmoreGomoryTSP.MinCost


theorem solution {n : ℕ} (φ ψ : Equiv.Perm (Fin (n + 1)))
    (hψ : IsTour ψ) : (graphStar φ ψ).Connected := by
  exact l7_core φ ψ hψ
