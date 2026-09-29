-- Prove2me | solution 1 for MetricTSP.hk_value_le_of_feasible
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-24T19:22:40.517279+00:00
-- url     : https://prove2.me/submissions/5f98df2b-d0e9-4ea6-b813-5f53622d4bb9

import Mathlib
import Definitions.Def_MetricTSP_model

namespace MetricTSP

variable {n : ℕ}

/-- Off-diagonal costs of a metric are nonnegative. -/
lemma metric_nonneg {c : Fin n → Fin n → ℝ} (hc : IsMetricCost c) (u v : Fin n) :
    0 ≤ c u v := by
  obtain ⟨hsym, hdiag, htri⟩ := hc
  have h := htri u v u
  rw [hdiag u, hsym v u] at h
  linarith

theorem hk_le_of_feasible (n : ℕ) (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c)
    (x : Fin n → Fin n → ℝ) (hx : IsHeldKarp x) :
    hkValue c ≤ (1 / 2) * ∑ u, ∑ v, c u v * x u v := by
  have hc0 : ∀ u v, 0 ≤ c u v := metric_nonneg hc
  have hbdd : BddBelow {t : ℝ | ∃ x : Fin n → Fin n → ℝ, IsHeldKarp x ∧
      t = (1 / 2) * ∑ u, ∑ v, c u v * x u v} := by
    refine ⟨0, ?_⟩
    rintro t ⟨z, hz, rfl⟩
    have hz0 : ∀ u v, 0 ≤ z u v := hz.2.2.1
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg; intro u _
    apply Finset.sum_nonneg; intro v _
    exact mul_nonneg (hc0 u v) (hz0 u v)
  unfold hkValue
  refine csInf_le hbdd ?_
  exact ⟨x, hx, rfl⟩

end MetricTSP

open MetricTSP

theorem solution (n : ℕ) (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c)
    (x : Fin n → Fin n → ℝ) (hx : IsHeldKarp x) :
    hkValue c ≤ (1 / 2) * ∑ u, ∑ v, c u v * x u v :=
  MetricTSP.hk_le_of_feasible n c hc x hx
