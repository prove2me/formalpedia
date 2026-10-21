-- Prove2me | solution 1 for GraphLQGame.Equilibrium.transitive_regular
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:32:19.107454+00:00
-- url     : https://prove2.me/submissions/97cce1b7-878a-4575-b351-218129ec6b40

import Mathlib
import Definitions.Def_GraphLQGame_Equilibrium_Graph

set_option autoImplicit false
open GraphLQGame.Equilibrium

lemma deg_iso {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (φ : G ≃g G) (v : Fin n) :
    G.degree (φ v) = G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_equiv φ.symm.toEquiv
  intro i
  simp only [SimpleGraph.mem_neighborFinset]
  constructor
  · intro h
    have := φ.symm.map_adj_iff.mpr h
    simpa using this
  · intro h
    have := φ.symm.map_adj_iff.mpr (φ.map_adj_iff.mpr h)
    simpa using (φ.map_adj_iff.mpr h)

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hT : IsTransitive G) (hN : NoIsolated G) :
    (∀ u v : Fin n, G.degree u = G.degree v) ∧
      (∀ v : Fin n, lap G = ((G.degree v : ℝ))⁻¹ • G.adjMatrix ℝ - 1) ∧
      (lap G).transpose = lap G := by
  have hreg : ∀ u v : Fin n, G.degree u = G.degree v := by
    intro u v
    obtain ⟨φ, hφ⟩ := hT u v
    rw [← hφ, deg_iso]
  refine ⟨hreg, ?_, ?_⟩
  · intro v
    ext i j
    simp only [lap, Matrix.sub_apply, Matrix.smul_apply, SimpleGraph.adjMatrix_apply,
      Matrix.one_apply, smul_eq_mul]
    rw [hreg i v]
    by_cases h : G.Adj i j <;> simp [h]
  · ext i j
    simp only [lap, Matrix.transpose_apply]
    have hadj : G.Adj j i ↔ G.Adj i j := G.adj_comm j i
    rw [hreg j i]
    simp only [hadj, eq_comm (a := j) (b := i)]
