-- Prove2me | solution 1 for GlobalTheory.NTr.mem_ball1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:02:49.871821+00:00
-- url     : https://prove2.me/submissions/e18f3dea-5218-4312-87fe-426e2e7a289d

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfect

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.NTr
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [hU : Unram F E]
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace GlobalTheory.NTr
theorem _root_.solution {a : K} (ha : a ∈ Metric.closedBall (0 : K) 1) : ‖a‖ ≤ 1 := by simpa using ha
end GlobalTheory.NTr
