-- Prove2me | solution 1 for MetricTSP.christofides_tour
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-24T21:31:54.349411+00:00
-- url     : https://prove2.me/submissions/6f774c98-eb5e-4731-bfe0-6a9629c0c80e

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_graph_cost
import Theorems.Thm_MetricTSP_cheap_connected_subgraph
import Theorems.Thm_MetricTSP_parity_matching
import Theorems.Thm_MetricTSP_tour_of_parity_join

namespace MetricTSP

/-- **Christofides against the LP, assembled from its three ingredients.**
A connected subgraph of cost at most the LP objective, a matching on its
odd-degree vertices of cost at most half the LP objective, and the
Euler-shortcut glue combine into a tour within `3/2` of the objective. -/
theorem christofides_tour_thm (n : ℕ) (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ)
    (hc : IsMetricCost c) (x : Fin n → Fin n → ℝ) (hx : IsHeldKarp x) :
    ∃ π : Equiv.Perm (Fin n),
      tourCost c π ≤ (3 / 2) * ((1 / 2) * ∑ u, ∑ v, c u v * x u v) := by
  classical
  obtain ⟨G, hG, hGcost⟩ := cheap_connected_subgraph n hn c hc x hx
  haveI : DecidableRel G.Adj := Classical.decRel _
  set T : Finset (Fin n) := Finset.univ.filter (fun v => Odd (G.degree v)) with hT
  have hTeven : Even T.card := by
    simpa [hT] using G.even_card_odd_degree_vertices
  obtain ⟨f, hfT, hfid, hfcost⟩ := parity_matching n hn c hc x hx T hTeven
  have hinv : ∀ v, f (f v) = v := by
    intro v
    by_cases hv : v ∈ T
    · exact (hfT v hv).2.1
    · rw [hfid v hv, hfid v hv]
  have hodd : ∀ v, f v ≠ v ↔ Odd (G.degree v) := by
    intro v
    constructor
    · intro hne
      by_cases hv : v ∈ T
      · have := Finset.mem_filter.mp (hT ▸ hv)
        exact this.2
      · exact absurd (hfid v hv) hne
    · intro hdeg
      have hv : v ∈ T := by
        rw [hT]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hdeg⟩
      exact (hfT v hv).2.2
  obtain ⟨π, hπ⟩ := tour_of_parity_join n hn c hc G hG f hinv hodd
  refine ⟨π, ?_⟩
  have hzero : ∀ v ∈ Finset.univ, v ∉ T → c v (f v) = 0 := by
    intro v _ hv
    rw [hfid v hv]
    exact hc.2.1 v
  have hsum : ∑ v, c v (f v) = ∑ v ∈ T, c v (f v) :=
    (Finset.sum_subset (Finset.subset_univ T) hzero).symm
  rw [hsum] at hπ
  linarith

end MetricTSP

open MetricTSP

theorem solution (n : ℕ) (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ)
    (hc : IsMetricCost c) (x : Fin n → Fin n → ℝ) (hx : IsHeldKarp x) :
    ∃ π : Equiv.Perm (Fin n),
      tourCost c π ≤ (3 / 2) * ((1 / 2) * ∑ u, ∑ v, c u v * x u v) :=
  MetricTSP.christofides_tour_thm n hn c hc x hx
