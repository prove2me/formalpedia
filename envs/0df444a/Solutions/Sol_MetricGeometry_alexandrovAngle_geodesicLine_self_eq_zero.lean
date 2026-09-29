-- Prove2me | solution 1 for MetricGeometry.alexandrovAngle_geodesicLine_self_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T22:53:09.11826+00:00
-- url     : https://prove2.me/submissions/810799e3-afad-48d1-90d5-58bd171f3b9d

import Definitions.Def_metric_alexandrov_angle

open MetricGeometry Filter Topology

theorem solution {X : Type*} [PseudoMetricSpace X] (gamma : ℝ → X) (h : IsGeodesicLine gamma) :
    alexandrovAngle (gamma 0) gamma gamma = 0 := by
  have key : ∀ (g1 g2 : ℝ → X) (c : ℝ),
      (∀ s t : ℝ, 0 < s → 0 < t → comparisonAngle (gamma 0) (g1 s) (g2 t) = c) →
      alexandrovAngle (gamma 0) g1 g2 = c := by
    intro g1 g2 c hc
    have h1 : ∀ᶠ s in 𝓝[>] (0:ℝ), (0:ℝ) < s := eventually_mem_nhdsWithin
    have hev : ∀ᶠ st in ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ))),
        comparisonAngle (gamma 0) (g1 st.1) (g2 st.2) = c :=
      (h1.prod_mk h1).mono (fun st hst => hc _ _ hst.1 hst.2)
    rw [alexandrovAngle, limsup_congr hev, limsup_const]
  refine key _ _ _ (fun s t hs ht => ?_)
  have e1 : dist (gamma 0) (gamma s) = s := by rw [h, abs_of_nonpos (by linarith)]; ring
  have e2 : dist (gamma 0) (gamma t) = t := by rw [h, abs_of_nonpos (by linarith)]; ring
  have e3 : dist (gamma s) (gamma t) = |s - t| := h s t
  rw [comparisonAngle, e1, e2, e3]
  have hq : (s ^ 2 + t ^ 2 - |s - t| ^ 2) / (2 * s * t) = 1 := by
    rw [sq_abs]; field_simp; ring
  rw [hq, Real.arccos_one]
