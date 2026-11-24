-- Prove2me | solution 1 for GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:27:37.925839+00:00
-- url     : https://prove2.me/submissions/93d39853-5952-4542-8898-8e2566259f12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Theorems.Thm_GlobalTheory_SCV_analyticAt_of_differentiableOn

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
theorem _root_.solution {f : E → V} {c : E} :
    AnalyticAt ℂ f c ↔ ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ f z :=
  ⟨fun h => h.eventually_analyticAt.mono fun _ hz => hz.differentiableAt,
    fun h => analyticAt_of_differentiableOn (s := {z | DifferentiableAt ℂ f z})
      (fun _ hz => DifferentiableAt.differentiableWithinAt hz) h⟩
end GlobalTheory.SCV
