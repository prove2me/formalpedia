-- Prove2me | solution 1 for NonsmoothNewton.Shared.exists_local_clarkeJac_subset_thickening
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T23:06:07.689983+00:00
-- url     : https://prove2.me/submissions/9eec46af-9c61-46e1-aae4-fcf3901fa144

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Theorems.Thm_NonsmoothNewton_Shared_exists_local_bJac_subset_thickening
open Filter Topology Set
open NonsmoothNewton.Shared
theorem solution {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (F : E → G) (hF : LocallyLipschitz F) (x : E)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y, dist y x < δ →
      clarkeJac F y ⊆
        Metric.thickening ε (clarkeJac F x) := by
  rcases exists_local_bJac_subset_thickening
      F hF x hε with ⟨δ, hδ, hb⟩
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  change convexHull ℝ (bJac F y) ⊆
    Metric.thickening ε (convexHull ℝ (bJac F x))
  have hmono :
      Metric.thickening ε (bJac F x) ⊆
        Metric.thickening ε
          (convexHull ℝ (bJac F x)) :=
    Metric.thickening_subset_of_subset ε
      (subset_convexHull ℝ (bJac F x))
  apply convexHull_min
  · exact (hb y hy).trans hmono
  · exact
      (convex_convexHull ℝ (bJac F x)).thickening ε
