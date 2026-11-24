-- Prove2me | solution 1 for GlobalTheory.PeriodSymm.dbar_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:24:36.489505+00:00
-- url     : https://prove2.me/submissions/9f463c11-e173-496d-95bd-f3bd9c27f3ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SetIntegralFderivEqZeroOfLatticePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CauchyRiemannIffDifferentiableOnComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PeriodicCechCocycleSmoothCoboundaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaCocyclePeriodicNonvanishingSections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open Filter Topology
open GlobalTheory GlobalTheory.PeriodSymm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.PeriodSymm
theorem _root_.solution {f : E → ℂ} {z : E} (h : ContDiffAt ℝ 2 f z) (u : E) :
    ContDiffAt ℝ 1 (dbar f u) z := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) z := h.fderiv_right (by norm_num)
  exact (h1.clm_apply contDiffAt_const).add (contDiffAt_const.mul (h1.clm_apply contDiffAt_const))
end GlobalTheory.PeriodSymm
