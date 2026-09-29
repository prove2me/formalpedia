-- Prove2me | solution 1 for MetricGeometry.alexandrovAngle_reparam
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T02:01:00.586385+00:00
-- url     : https://prove2.me/submissions/1dd95c6d-afcf-4cdf-aaf7-1efdbbaf5ca8

import Definitions.Def_metric_alexandrov_angle

open MetricGeometry Filter Topology

theorem solution {X : Type*} [PseudoMetricSpace X] (p : X) (g h : ℝ → X)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    alexandrovAngle p (fun t => g (a * t)) (fun t => h (b * t))
      = alexandrovAngle p g h := by
  have hmapgen : ∀ c : ℝ, 0 < c →
      Filter.map (fun s : ℝ => c * s) (𝓝[>] (0:ℝ)) = 𝓝[>] (0:ℝ) := by
    intro c hc
    have hsurj : Function.Surjective (fun s : ℝ => c * s) :=
      fun y => ⟨c⁻¹ * y, by field_simp⟩
    calc Filter.map (fun s : ℝ => c * s) (𝓝[>] (0:ℝ))
        = Filter.map (fun s : ℝ => c * s)
            (Filter.comap (fun s : ℝ => c * s) (𝓝[>] (0:ℝ))) := by
          rw [comap_mulLeft_nhdsGT_zero hc]
      _ = 𝓝[>] (0:ℝ) := Filter.map_comap_of_surjective hsurj _
  have hprod : Filter.map (fun st : ℝ × ℝ => (a * st.1, b * st.2))
      ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ))) = (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)) := by
    rw [← Filter.prod_map_map_eq, hmapgen a ha, hmapgen b hb]
  show Filter.limsup
      ((fun st : ℝ × ℝ => comparisonAngle p (g st.1) (h st.2)) ∘
        (fun st : ℝ × ℝ => (a * st.1, b * st.2)))
      ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ))) = _
  rw [Filter.limsup_comp, hprod]
  rfl
