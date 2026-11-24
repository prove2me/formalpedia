-- Prove2me | solution 1 for GlobalTheory.SCV.eqOn_of_eventuallyEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:14:57.580589+00:00
-- url     : https://prove2.me/submissions/aaac1a1e-3123-43d4-a55b-1aeef84cfd05

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
theorem _root_.solution {f g : E → V} {U : Set E} (hU : IsOpen U) (hU' : IsPreconnected U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) {c : E} (hc : c ∈ U)
    (hfg : f =ᶠ[𝓝 c] g) : EqOn f g U :=
  (analyticOnNhd_of_differentiableOn hU hf).eqOn_of_preconnected_of_eventuallyEq
    (analyticOnNhd_of_differentiableOn hU hg) hU' hc hfg
end GlobalTheory.SCV
