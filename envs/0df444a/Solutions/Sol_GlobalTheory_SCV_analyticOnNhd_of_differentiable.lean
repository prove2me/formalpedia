-- Prove2me | solution 1 for GlobalTheory.SCV.analyticOnNhd_of_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:14:56.614833+00:00
-- url     : https://prove2.me/submissions/d50706f2-99db-44a2-8ac2-57606c975128

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
theorem _root_.solution {f : E → V} (hf : Differentiable ℂ f) (s : Set E) :
    AnalyticOnNhd ℂ f s :=
  fun c _ => analyticOnNhd_of_differentiableOn isOpen_univ hf.differentiableOn c (mem_univ c)
end GlobalTheory.SCV
