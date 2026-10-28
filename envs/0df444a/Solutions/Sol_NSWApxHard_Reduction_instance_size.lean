-- Prove2me | solution 1 for NSWApxHard.Reduction.instance_size
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T00:32:30.343569+00:00
-- url     : https://prove2.me/submissions/0380e0ab-5ead-480c-8189-312a158bd6b3

import Mathlib
import Definitions.Def_NSWApxHard_Reduction_Instance

open NSWApxHard.Reduction Finset

lemma deg3 {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] (hG : IsCubic G) (v : Fin N) :
    G.degree v = 3 := by
  rw [← hG v, ← SimpleGraph.card_neighborFinset_eq_degree, Set.ncard_eq_toFinset_card']
  rfl

lemma card_edges {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] (hG : IsCubic G) :
    2 * #G.edgeFinset = 3 * N := by
  rw [← G.sum_degrees_eq_twice_card_edges]
  simp [deg3 hG]
  ring

lemma card_inc {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] (hG : IsCubic G) :
    Fintype.card (Inc G) = 3 * N := by
  rw [Fintype.card_subtype, card_filter, Fintype.sum_prod_type]
  have : ∀ v : Fin N, (∑ e : Sym2 (Fin N), if e ∈ G.edgeFinset ∧ v ∈ e then 1 else 0) = 3 := by
    intro v
    rw [← card_filter, ← deg3 hG v, ← SimpleGraph.card_incidenceFinset_eq_degree]
    congr 1
    ext e
    simp [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet]
  simp only [this, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  ring

theorem solution {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (k : ℕ)
    (hG : IsCubic G) :
    2 * Fintype.card (Agent G) = 5 * N ∧ 2 * Fintype.card (Item G k) = 2 * k + 9 * N := by
  have h1 := card_edges hG
  have h2 := card_inc hG
  simp only [Agent, Item, Edge, Fintype.card_sum, Fintype.card_coe, Fintype.card_fin]
  omega
