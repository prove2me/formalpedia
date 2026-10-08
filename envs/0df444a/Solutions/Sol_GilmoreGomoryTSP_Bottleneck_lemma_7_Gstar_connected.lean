-- Prove2me | solution 1 for GilmoreGomoryTSP.Bottleneck.lemma_7_Gstar_connected
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:59:28.669732+00:00
-- url     : https://prove2.me/submissions/cd210be8-b14d-4285-91c5-77d3dae7df41

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_Bottleneck_Model

set_option backward.isDefEq.respectTransparency false
open GilmoreGomoryTSP.Bottleneck

private theorem interval_reach {n : ℕ} (G : SimpleGraph (Fin (n + 1))) (a b : Fin (n + 1))
    (hab : a.val ≤ b.val)
    (hedge : ∀ q : Fin n, a.val ≤ q.val → q.val < b.val → G.Adj q.castSucc q.succ) :
    G.Reachable a b := by
  have h : ∀ m (hm : m < n + 1), a.val ≤ m → m ≤ b.val → G.Reachable a ⟨m, hm⟩ := by
    intro m
    induction m with
    | zero =>
      intro hm ha hb
      have he : a = ⟨0, hm⟩ := Fin.ext (by dsimp; omega)
      subst a
      exact SimpleGraph.Reachable.refl _
    | succ m ih =>
      intro hm ha hb
      by_cases he : a.val = m + 1
      · have he' : a = ⟨m + 1, hm⟩ := Fin.ext he
        subst a
        exact SimpleGraph.Reachable.refl _
      · have hr := ih (by omega) (by omega) (by omega)
        have hh := hedge ⟨m, by omega⟩ (by dsimp; omega) (by dsimp; omega)
        exact hr.trans hh.reachable
  exact h b.val b.isLt hab le_rfl

private theorem reach_phi {n : ℕ} (φ ψ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    (Gstar φ ψ).Reachable i (φ i) := by
  by_cases h : i = φ i
  · rw [← h]
  · apply SimpleGraph.Adj.reachable
    exact Or.inl (by simp [graphOf, SimpleGraph.fromRel, h])

private theorem reach_psi {n : ℕ} (φ ψ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    (Gstar φ ψ).Reachable i (ψ i) := by
  let j := φ.symm (ψ i)
  have hr : (Gstar φ ψ).Reachable i j := by
    rcases le_total i.val j.val with hij | hji
    · apply interval_reach _ i j hij
      intro q hq hqj
      apply Or.inr
      have hmem : q ∈ starArcs φ ψ := by
        simp only [starArcs, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inl ⟨i, hq, hqj⟩
      exact (by simp [adjArcs, SimpleGraph.fromRel, Fin.ext_iff]; exact Or.inl ⟨q, hmem, rfl⟩)
    · apply SimpleGraph.Reachable.symm
      apply interval_reach _ j i hji
      intro q hq hqi
      apply Or.inr
      have hmem : q ∈ starArcs φ ψ := by
        simp only [starArcs, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inr ⟨i, hq, hqi⟩
      exact (by simp [adjArcs, SimpleGraph.fromRel, Fin.ext_iff]; exact Or.inl ⟨q, hmem, rfl⟩)
  have hp := reach_phi φ ψ j
  simpa [j] using hr.trans hp

theorem solution {n : ℕ} (φ ψ : Equiv.Perm (Fin (n + 1)))
    (hψ : GilmoreGomoryTSP.MinCost.IsTour ψ) : (Gstar φ ψ).Connected := by
  classical
  refine ⟨?_⟩
  intro a b
  let s := Finset.univ.filter (fun v => (Gstar φ ψ).Reachable a v)
  have hs : s.Nonempty := ⟨a, by simp [s]⟩
  have hm : s.map ψ.toEmbedding ⊆ s := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hv
    have hu' : (Gstar φ ψ).Reachable a u := by simpa [s] using hu
    simpa [s] using hu'.trans (reach_psi φ ψ u)
  have he : s.map ψ.toEmbedding = s := Finset.eq_of_subset_of_card_le hm (by simp)
  have hu : s = Finset.univ := by
    by_contra h
    exact hψ s hs h he
  have hb : b ∈ s := by rw [hu]; simp
  simpa [s] using hb

#print axioms solution
