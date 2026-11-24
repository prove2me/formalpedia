-- Prove2me | solution 1 for GlobalTheory.Published.LogLine.continuousOn_logPartial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:40:00.442571+00:00
-- url     : https://prove2.me/submissions/98c99ae7-5f33-467a-a9ff-511f5a84821a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__ExistsHorizontalGeneratorOfCharts_f0ad16e2bc421ec8
import Theorems.Thm_GlobalTheory_SCV_differentiableOn_fderiv_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology
open GlobalTheory GlobalTheory.Published GlobalTheory.Published.LogLine
variable {n : ℕ}
namespace GlobalTheory.Published.LogLine
theorem _root_.solution {U : Set (Fin n → ℂ)} (hU : IsOpen U) (S : Finset (Fin n))
    (i : Fin n) {F : (Fin n → ℂ) → ℂ} (hF : DifferentiableOn ℂ F U) :
    ContinuousOn (logPartial S i F) U := by
  refine ContinuousOn.mul ?_ (GlobalTheory.SCV.differentiableOn_fderiv_apply hU hF _).continuousOn
  split_ifs <;> fun_prop
end GlobalTheory.Published.LogLine
