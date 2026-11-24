-- Prove2me | solution 1 for GlobalTheory.SCV.contDiffAt_of_differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:27:36.990879+00:00
-- url     : https://prove2.me/submissions/68ceb2a2-9d0b-4dec-8a06-3b1918ba9085

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
theorem _root_.solution {f : E → V} {s : Set E} {c : E}
    (hf : DifferentiableOn ℂ f s) (hs : s ∈ 𝓝 c) (n : WithTop ℕ∞) : ContDiffAt ℂ n f c :=
  (analyticAt_of_differentiableOn hf hs).contDiffAt
end GlobalTheory.SCV
