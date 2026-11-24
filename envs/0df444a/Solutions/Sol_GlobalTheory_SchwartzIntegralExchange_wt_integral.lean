-- Prove2me | solution 1 for GlobalTheory.SchwartzIntegralExchange.wt_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:17:05.370337+00:00
-- url     : https://prove2.me/submissions/d9f5d4ce-cafc-4976-bf11-22ae72fbcdf3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzIntegralSuperposition
import Theorems.Thm_GlobalTheory_SchwartzIntegralExchange_wt_apply
import Theorems.Thm_GlobalTheory_SchwartzIntegralExchange_iteratedFDeriv_integral
import Theorems.Thm_GlobalTheory_SchwartzIntegralExchange_integrable_wt

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
    (u : SchwartzMap E ℂ) (hu : ∀ x, u x = ∫ ξ, c ξ * Φ ξ x ∂ν) (k n : ℕ) :
    wt k n u = ∫ ξ, c ξ • wt k n (Φ ξ) ∂ν := by
  ext1 x
  have := (BoundedContinuousFunction.evalCLM ℂ x).integral_comp_comm
    (integrable_wt hΦ hc hi k n)
  simp only [BoundedContinuousFunction.evalCLM_apply] at this
  rw [← this, wt_apply, iteratedFDeriv_integral hΦ hc hi u hu n x, ← integral_smul]
  congr 1
  funext ξ
  rw [BoundedContinuousFunction.smul_apply, wt_apply, smul_comm]
end GlobalTheory.SchwartzIntegralExchange
