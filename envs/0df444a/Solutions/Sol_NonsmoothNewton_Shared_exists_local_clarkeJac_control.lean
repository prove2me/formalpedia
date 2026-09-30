-- Prove2me | solution 1 for NonsmoothNewton.Shared.exists_local_clarkeJac_control
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T20:32:34.231086+00:00
-- url     : https://prove2.me/submissions/1cfb6982-7960-4837-883f-95ca3db68b72

import Mathlib
import Theorems.Thm_NonsmoothNewton_Shared_exists_local_bJac_control
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
open Filter Topology Set
open NonsmoothNewton.Shared
theorem solution
    {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (F : E → G) (hF : LocallyLipschitz F) (x : E) :
    ∃ K : NNReal, ∃ r : ℝ, 0 < r ∧
      (∀ y ∈ Metric.ball x r, (clarkeJac F y).Nonempty) ∧
      (∀ y ∈ Metric.ball x r,
        ∀ V ∈ clarkeJac F y, ‖V‖ ≤ (K : ℝ)) := by
  rcases exists_local_bJac_control F hF x with
    ⟨K, r, hr, _, hne, hbound⟩
  refine ⟨K, r, hr, ?_, ?_⟩
  · intro y hy
    rcases hne y hy with ⟨V, hV⟩
    refine ⟨V, ?_⟩
    change V ∈ convexHull ℝ (bJac F y)
    exact subset_convexHull ℝ (bJac F y) hV
  · intro y hy V hV
    change V ∈ convexHull ℝ (bJac F y) at hV
    have hsub :
        bJac F y ⊆ Metric.closedBall 0 (K : ℝ) := by
      intro W hW
      rw [mem_closedBall_zero_iff]
      exact hbound y hy W hW
    have hHull :
        convexHull ℝ (bJac F y) ⊆
          Metric.closedBall 0 (K : ℝ) :=
      convexHull_min hsub (convex_closedBall (0 : E →L[ℝ] G) (K : ℝ))
    exact mem_closedBall_zero_iff.mp (hHull hV)
