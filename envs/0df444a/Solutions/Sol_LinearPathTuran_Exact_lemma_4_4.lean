-- Prove2me | solution 1 for LinearPathTuran.Exact.lemma_4_4
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:25:50.381055+00:00
-- url     : https://prove2.me/submissions/73267d7a-3d56-4dd5-bdd0-6a002bdd9efa

import Mathlib
import Theorems.Thm_EvenCycleTuran_EvenCount_theorem_2

set_option autoImplicit false


open Finset

theorem solution (n c : ℕ) (hc : 3 ≤ c) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → p.length < c) :
    2 * #G.edgeFinset ≤ (c - 1) * (n - 1) := by
  have h := EvenCycleTuran.EvenCount.theorem_2 n (c - 1) (by omega) G ?_
  · exact h
  intro a ha hcont
  obtain ⟨v, p, hp, hlen⟩ := (SimpleGraph.cycleGraph_isContained_iff (by omega)).mp hcont
  have := hG v p hp
  omega
