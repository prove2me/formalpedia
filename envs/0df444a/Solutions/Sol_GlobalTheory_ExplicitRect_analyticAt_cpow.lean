-- Prove2me | solution 1 for GlobalTheory.ExplicitRect.analyticAt_cpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:02.971102+00:00
-- url     : https://prove2.me/submissions/e21361f3-24c4-42db-85b5-0bb3de8e9f83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BdIntEqZeroOfPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CompletedLFunctionNeZeroOfReNonpos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AnalyticAtDslope

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ExplicitRect
namespace GlobalTheory.ExplicitRect
theorem _root_.solution {u : ℝ} (hu : 0 < u) (p : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => (u : ℂ) ^ s) p := analyticAt_const.cpow analyticAt_id (Complex.ofReal_mem_slitPlane.2 hu)
end GlobalTheory.ExplicitRect
