-- Prove2me | solution 1 for Kyprianou.Ch04.bvContDiffSpatialEvalTendstoV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:32:47.967889+00:00
-- url     : https://prove2.me/submissions/868f3b0d-5972-4ef4-ac09-cb84e23d6dfd

import Mathlib
open MeasureTheory Filter Set
set_option autoImplicit false

theorem solution
    {I : Type} (L : Filter I)
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (u : ℝ) (hu : 0 ≤ u) (G : I → ℝ) (g : ℝ)
    (h : Tendsto G L (nhds g)) :
    Tendsto (fun i => f (u,G i)) L (nhds (f (u,g))) := by
  have hc : Continuous (fun x : ℝ => f (u,x)) := by
    apply continuousOn_univ.mp
    exact hf.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x _ => ⟨hu, mem_univ _⟩)
  exact (hc.continuousAt.tendsto.comp h)
