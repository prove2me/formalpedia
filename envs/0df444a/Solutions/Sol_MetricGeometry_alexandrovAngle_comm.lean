-- Prove2me | solution 1 for MetricGeometry.alexandrovAngle_comm
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T23:03:04.967126+00:00
-- url     : https://prove2.me/submissions/8b1cd4e6-780b-4936-8174-ad8a8c816034

import Definitions.Def_metric_alexandrov_angle
import Theorems.Thm_MetricGeometry_comparisonAngle_comm

open MetricGeometry Filter Topology

theorem solution {X : Type*} [PseudoMetricSpace X] (p : X) (g1 g2 : ℝ → X) :
    alexandrovAngle p g1 g2 = alexandrovAngle p g2 g1 := by
  set F : Filter (ℝ × ℝ) := (𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ)) with hF
  set u : ℝ × ℝ → ℝ := fun st => comparisonAngle p (g1 st.1) (g2 st.2) with hu
  have hmap : Filter.map (Prod.swap : ℝ × ℝ → ℝ × ℝ) F = F := by
    rw [hF]; exact Filter.prod_comm.symm
  have hswap : (fun st : ℝ × ℝ => comparisonAngle p (g2 st.1) (g1 st.2)) = u ∘ Prod.swap := by
    funext st; exact comparisonAngle_comm p (g2 st.1) (g1 st.2)
  show Filter.limsup u F = Filter.limsup (fun st : ℝ × ℝ => comparisonAngle p (g2 st.1) (g1 st.2)) F
  rw [hswap, Filter.limsup_comp, hmap]
