-- Prove2me | solution 1 for GlobalTheory.QuadFibre.IsSqrtOn.norm_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:47:52.203549+00:00
-- url     : https://prove2.me/submissions/3e5bd853-2040-4bec-8f65-e74130bb7131

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FibOfZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegrableContinuousOnAveragedFibreIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped Pointwise
open GlobalTheory GlobalTheory.QuadFibre
namespace GlobalTheory.QuadFibre
namespace IsSqrtOn
theorem _root_.solution {K : Type} [NormedField K] {U : Set K} {s : K → K}
    (h : IsSqrtOn U s) {a : K} (ha : a ∈ U) : ‖s a‖ = 1 := by
  obtain ⟨-, -, -, -, -, hnorm, -, hsq⟩ := h
  have h2 : ‖s a‖ ^ 2 = 1 := by rw [← norm_pow, hsq a ha, hnorm a ha]
  have h0 := norm_nonneg (s a)
  nlinarith [sq_nonneg (‖s a‖ - 1)]
end IsSqrtOn
end GlobalTheory.QuadFibre
