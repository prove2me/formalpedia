-- Prove2me | solution 1 for GlobalTheory.TraceUnit.norm_sq_sub_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:38:56.460085+00:00
-- url     : https://prove2.me/submissions/b18f9bce-f171-4726-94f6-40299c6ea44a

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralTraceUnitUnramifiedQuadratic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.TraceUnit
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace GlobalTheory.TraceUnit
theorem _root_.solution {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖x ^ 2 - y ^ 2‖ ≤ ‖x - y‖ := by
  have h1 : x ^ 2 - y ^ 2 = (x - y) * (x + y) := by ring
  rw [h1, norm_mul]
  have h2 : ‖x + y‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  calc ‖x - y‖ * ‖x + y‖ ≤ ‖x - y‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = ‖x - y‖ := mul_one _
end GlobalTheory.TraceUnit
