-- Prove2me | solution 1 for MetricTSP.wolsey_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-24T21:32:08.08243+00:00
-- url     : https://prove2.me/submissions/23c1ca5b-0b46-4f49-ab31-fca2f154c1c5

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_tour_vector
import Theorems.Thm_MetricTSP_christofides_tour
import Theorems.Thm_MetricTSP_tsp_opt_le_tour_cost
import Theorems.Thm_MetricTSP_tour_vector_held_karp

namespace MetricTSP

/-- **Wolsey 1980.** Running the Christofides analysis against the Held–Karp
relaxation: every feasible LP point admits a tour within `3/2` of its objective,
so the optimum is within `3/2` of the LP value. -/
theorem wolsey (n : ℕ) (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ)
    (hc : IsMetricCost c) :
    tspOpt c ≤ 3 / 2 * hkValue c := by
  have hkey : ∀ t ∈ {t : ℝ | ∃ x : Fin n → Fin n → ℝ, IsHeldKarp x ∧
      t = (1 / 2) * ∑ u, ∑ v, c u v * x u v}, (2 / 3) * tspOpt c ≤ t := by
    rintro t ⟨x, hx, rfl⟩
    obtain ⟨π, hπ⟩ := christofides_tour n hn c hc x hx
    have h2 := tsp_opt_le_tour_cost n c hc π
    linarith
  have hne : {t : ℝ | ∃ x : Fin n → Fin n → ℝ, IsHeldKarp x ∧
      t = (1 / 2) * ∑ u, ∑ v, c u v * x u v}.Nonempty :=
    ⟨(1 / 2) * ∑ u, ∑ v, c u v * tourVec 1 u v, tourVec 1,
      tour_vector_held_karp n hn 1, rfl⟩
  have hinf : (2 / 3) * tspOpt c ≤ hkValue c := by
    unfold hkValue
    exact le_csInf hne hkey
  linarith

end MetricTSP

open MetricTSP

theorem solution (n : ℕ) (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ)
    (hc : IsMetricCost c) :
    tspOpt c ≤ 3 / 2 * hkValue c :=
  MetricTSP.wolsey n hn c hc
