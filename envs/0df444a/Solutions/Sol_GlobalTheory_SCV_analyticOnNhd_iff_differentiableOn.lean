-- Prove2me | solution 1 for GlobalTheory.SCV.analyticOnNhd_iff_differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:15:31.598459+00:00
-- url     : https://prove2.me/submissions/33e06d50-f1cb-4ee6-8cec-5c50e0950391

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Theorems.Thm_GlobalTheory_SCV_analyticOnNhd_of_differentiableOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter
open scoped Topology ContDiff Nat
open GlobalTheory GlobalTheory.SCV
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
namespace GlobalTheory.SCV
theorem _root_.solution {f : E → V} {U : Set E} (hU : IsOpen U) :
    AnalyticOnNhd ℂ f U ↔ DifferentiableOn ℂ f U :=
  ⟨AnalyticOnNhd.differentiableOn, analyticOnNhd_of_differentiableOn hU⟩
end GlobalTheory.SCV
