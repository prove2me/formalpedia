-- Prove2me | solution 1 for GlobalTheory.SchwartzIntegralExchange.integrable_iteratedFDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:50:26.674847+00:00
-- url     : https://prove2.me/submissions/4720d12b-f363-46e8-8e8b-7c94c86bbb5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzIntegralSuperposition
import Theorems.Thm_GlobalTheory_SchwartzIntegralExchange_continuous_iteratedFDeriv_at

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
    (n : ℕ) (x : E) : Integrable (fun ξ => c ξ • iteratedFDeriv ℝ n (Φ ξ) x) ν := by
  refine (hi 0 n).mono' (hc.smul
    ((continuous_iteratedFDeriv_at n x).comp hΦ).aestronglyMeasurable) (ae_of_all _ fun ξ => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ _ n x)
    (norm_nonneg _)
end GlobalTheory.SchwartzIntegralExchange
