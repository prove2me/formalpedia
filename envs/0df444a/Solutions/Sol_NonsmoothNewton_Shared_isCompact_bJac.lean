-- Prove2me | solution 1 for NonsmoothNewton.Shared.isCompact_bJac
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T23:42:51.627447+00:00
-- url     : https://prove2.me/submissions/941bd9d0-6ecb-4447-ac76-67bf74572dff

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Theorems.Thm_NonsmoothNewton_Shared_exists_local_bJac_control
import Theorems.Thm_NonsmoothNewton_Shared_bJac_mem_of_tendsto
open Filter Topology Set
open NonsmoothNewton.Shared
theorem solution {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (F : E → G) (hF : LocallyLipschitz F) (x : E) :
    IsCompact (bJac F x) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  refine ⟨?_, ?_⟩
  · apply IsSeqClosed.isClosed
    intro Vseq V hmem hV
    exact bJac_mem_of_tendsto
      (xseq := fun _ => x)
      (Vseq := Vseq)
      tendsto_const_nhds hV hmem
  · rcases exists_local_bJac_control F hF x with
      ⟨K, r, hr, _, _, hbound⟩
    rw [Metric.isBounded_iff_subset_closedBall
      (0 : E →L[ℝ] G)]
    refine ⟨(K : ℝ), ?_⟩
    intro V hV
    rw [mem_closedBall_zero_iff]
    exact hbound x (Metric.mem_ball_self hr) V hV
