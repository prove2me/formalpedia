-- Prove2me | solution 1 for GlobalTheory.SchwartzIntegralExchange.integrable_wt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:45.689572+00:00
-- url     : https://prove2.me/submissions/0f6d87ee-11ab-4917-8b56-4b955af66739

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzIntegralSuperposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
open GlobalTheory.SchwartzIntegralExchange
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {P : Type} [TopologicalSpace P] [SecondCountableTopology P] [MeasurableSpace P]
  [OpensMeasurableSpace P] {ν : Measure P} {Φ : P → SchwartzMap E ℂ} {c : P → ℂ}
namespace GlobalTheory.SchwartzIntegralExchange
theorem _root_.solution (hΦ : Continuous Φ) (hc : AEStronglyMeasurable c ν)
    (hi : ∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ)) ν)
    (k n : ℕ) : Integrable (fun ξ => c ξ • wt k n (Φ ξ)) ν := by
  refine (hi k n).mono' (hc.smul
    ((wt k n).continuous.comp hΦ).aestronglyMeasurable) (ae_of_all _ fun ξ => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_wtFun_le k n _) (norm_nonneg _)
end GlobalTheory.SchwartzIntegralExchange
