-- Prove2me | solution 1 for GlobalTheory.SCV.contDiff_of_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:28:43.235807+00:00
-- url     : https://prove2.me/submissions/073a550e-5bc2-450c-b83d-4cc38cd86f09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Theorems.Thm_GlobalTheory_SCV_analyticOnNhd_of_differentiable

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
theorem _root_.solution {f : E → V} (hf : Differentiable ℂ f) (n : WithTop ℕ∞) :
    ContDiff ℂ n f :=
  (analyticOnNhd_of_differentiable hf univ).contDiff
end GlobalTheory.SCV
