-- Prove2me | solution 1 for GlobalTheory.isBigO_sub_linear_sq_of_analyticAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:01:30.813821+00:00
-- url     : https://prove2.me/submissions/7228d4a1-2e54-48c3-97e5-ac8aea35f6d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter Asymptotics
open scoped Topology
open GlobalTheory
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace GlobalTheory
theorem _root_.solution {f : E → F} {L : E →L[ℂ] F} (hf : AnalyticAt ℂ f 0)
    (h0 : f 0 = 0) (hL : HasFDerivAt f L 0) :
    (fun x => f x - L x) =O[𝓝 0] fun x => ‖x‖ ^ 2 := by
  obtain ⟨p, hp⟩ := hf
  have h1 := hp.isBigO_sub_partialSum_pow 2
  have h2 : L = continuousMultilinearCurryFin1 ℂ E F (p 1) := hL.unique hp.hasFDerivAt
  refine h1.congr_left fun x => ?_
  simp [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, hp.coeff_zero, h0, h2]
  congr 1
  ext i
  simp [Fin.snoc]
end GlobalTheory
