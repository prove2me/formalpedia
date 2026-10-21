-- Prove2me | solution 1 for ModernOnlineLearning.OGD.proposition_2_11
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-20T15:12:18.362031+00:00
-- url     : https://prove2.me/submissions/aa74a887-b450-448b-a39b-5360defafb43

import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

set_option autoImplicit false

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (V : Set E) (hV : V.Nonempty) (hc : IsClosed V)
    (hv : Convex ℝ V) (x p y : E) (hp : OnlineConvexOpt.FirstOrder.IsMetricProjection V x p)
    (hy : y ∈ V) : ‖p - y‖ ≤ ‖x - y‖ := by
  let : Nonempty V := ⟨⟨p, hp.1⟩⟩
  have hmin : ‖x - p‖ = ⨅ w : V, ‖x - w‖ := by
    apply le_antisymm
    · exact le_ciInf fun w => by simpa [dist_eq_norm] using hp.2 w w.property
    · have hb : BddBelow (Set.range (fun w : V => ‖x - (w : E)‖)) :=
        ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
      exact ciInf_le hb ⟨p, hp.1⟩
  have hang := (norm_eq_iInf_iff_real_inner_le_zero hv hp.1).mp hmin y hy
  have heq : (x - p) - (y - p) = x - y := by abel
  have hsq := norm_sub_sq_real (x - p) (y - p)
  rw [heq, norm_sub_rev y p] at hsq
  nlinarith [sq_nonneg ‖x - p‖, norm_nonneg (p - y), norm_nonneg (x - y)]
