-- Prove2me | solution 1 for HryniewiczCriterion.homogeneous_windingInterval_gt_one
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T15:26:20.863132+00:00
-- url     : https://prove2.me/submissions/2ecea645-88b0-4c45-9b4d-30d61ace9efd

import Theorems.Thm_HryniewiczCriterion_homogeneous_frame_flow_split
import Theorems.Thm_HryniewiczCriterion_positive_path_graph_angle_bound
import Theorems.Thm_HryniewiczCriterion_homogeneous_graph_angle_transport
import Theorems.Thm_HryniewiczCriterion_polar_angle_windingInterval_gt_one

open HryniewiczCriterion
open scoped ContDiff

theorem solution (K : R4 → ℝ) (hK : IsHomogeneousConvexModel K)
    (Q : PeriodicOrbit K) (Z : ℝ → (R4 →L[ℝ] R4)) (hZ : IsLinearizedFlow K Q.x Z) :
    ∀ d ∈ windingInterval (linearizedXiPath K Q Z), 1 < d := by
  obtain ⟨⟨hs, hdet, h0⟩, hY0, ⟨S, hSc, hSpos, hd⟩, hend⟩ :=
    homogeneous_frame_flow_split K hK Q Z hZ
  obtain ⟨θ, α, hθ, hα, hθα⟩ := homogeneous_graph_angle_transport K hK Q Z hZ
  have hC := positive_path_graph_angle_bound (frameFlowMatrix K Q Z) S Q.T Q.T_pos hSc hSpos
    hY0 hd _ hend θ hθ
  exact polar_angle_windingInterval_gt_one _ hs hdet h0 α hα (by linarith)
