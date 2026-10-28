-- Prove2me | solution 1 for KellyLossNetworks.Routing.mean_Y_gt_one
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T08:10:28.880416+00:00
-- url     : https://prove2.me/submissions/5251340d-76f6-4294-9a12-ace04ba83451

import Mathlib
import Definitions.Def_KellyLossNetworks_Routing_Model

open MeasureTheory Filter Topology

open KellyLossNetworks.Routing in
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (hnonneg : ∀ᵐ t ∂μ, 0 ≤ t)
    (C : ℝ) (hm : 0 < spareMean μ C) (ε : ℝ) (hε : 0 < ε) (hεm : ε < spareMean μ C ^ 2) :
    ∫ p, Yv μ C ε p ∂(μ.prod μ) = spareMean μ C ^ 2 / (spareMean μ C ^ 2 - ε) ∧
    1 < ∫ p, Yv μ C ε p ∂(μ.prod μ) := by
  have h1 : ∫ p, Yv μ C ε p ∂(μ.prod μ) = spareMean μ C ^ 2 / (spareMean μ C ^ 2 - ε) := by
    unfold Yv
    rw [integral_div, integral_prod_mul (fun t => max (C - t) 0) (fun t => max (C - t) 0)]
    unfold spareMean
    ring
  refine ⟨h1, ?_⟩
  rw [h1, one_lt_div (by linarith)]
  linarith
