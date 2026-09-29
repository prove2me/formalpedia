-- Prove2me | solution 1 for MetricGeometry.alexandrovAngle_eq_of_comparisonAngle_const
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T22:53:06.32849+00:00
-- url     : https://prove2.me/submissions/23902755-e0ef-4ab1-8604-267765722034

import Definitions.Def_metric_alexandrov_angle

open MetricGeometry Filter Topology

theorem solution {X : Type*} [PseudoMetricSpace X]
    (p : X) (g1 g2 : ℝ → X) (c : ℝ)
    (h : ∀ s t : ℝ, 0 < s → 0 < t → comparisonAngle p (g1 s) (g2 t) = c) :
    alexandrovAngle p g1 g2 = c := by
  have h1 : ∀ᶠ s in 𝓝[>] (0:ℝ), (0:ℝ) < s := eventually_mem_nhdsWithin
  have hev : ∀ᶠ st in ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ))),
      comparisonAngle p (g1 st.1) (g2 st.2) = c :=
    (h1.prod_mk h1).mono (fun st hst => h _ _ hst.1 hst.2)
  rw [alexandrovAngle, limsup_congr hev, limsup_const]
