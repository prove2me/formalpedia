-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_scale_convolution_vanishes_origin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:06:23.757549+00:00
-- url     : https://prove2.me/submissions/a0a86b09-bd77-44d8-a784-e0f888b7e0c7

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_q0_causal_integrable
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_origin_product_limit
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_convolution_small_interval_bound
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB Filter
open scoped Topology

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    Tendsto (fun x : ℝ => ∫ s in Set.Ioc (0 : ℝ) x,
        W 0 s * W q (x - s) ∂volume)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (0 : ℝ)) := by
  have hb := source_scale_convolution_small_interval_bound ψ W hW
  have hi := source_scale_q0_causal_integrable ψ W hW q
  have hlim := source_scale_origin_product_limit ψ W hW q hq
  have hlo : (fun _ : ℝ => (0 : ℝ)) ≤ᶠ[𝓝[>] (0 : ℝ)]
      (fun x : ℝ => ∫ s in Set.Ioc (0 : ℝ) x,
        W 0 s * W q (x - s) ∂volume) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < x at hx
    exact (hb q x hq hx.le (hi x hq hx.le)).1
  have hhi : (fun x : ℝ => ∫ s in Set.Ioc (0 : ℝ) x,
      W 0 s * W q (x - s) ∂volume) ≤ᶠ[𝓝[>] (0 : ℝ)]
      (fun x : ℝ => x * W 0 x * W q x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < x at hx
    exact (hb q x hq hx.le (hi x hq hx.le)).2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hlim hlo hhi
