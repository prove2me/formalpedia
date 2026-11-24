-- Prove2me | solution 1 for GlobalTheory.ExponentialIntegralUnits.mul_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:49:19.570845+00:00
-- url     : https://prove2.me/submissions/474a4e03-0b50-4264-830a-78d0ae5ba5c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsUnitIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NormedSpace Filter Topology
open GlobalTheory GlobalTheory.ExponentialIntegralUnits
universe u_1
variable {𝔸 : Type u_1} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
namespace GlobalTheory.ExponentialIntegralUnits
theorem _root_.solution (M : ℝ → 𝔸) (hc : Continuous M)
    (hadd : ∀ s t : ℝ, M (s + t) = M s * M t) (t δ : ℝ) :
    M t * (∫ s in (0 : ℝ)..δ, M s)
      = (∫ s in (0 : ℝ)..(t + δ), M s) - ∫ s in (0 : ℝ)..t, M s := by
  have hL := ((ContinuousLinearMap.mul ℝ 𝔸) (M t)).intervalIntegral_comp_comm (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 δ)
  simp only [ContinuousLinearMap.mul_apply'] at hL
  rw [← hL]
  simp_rw [← hadd]
  rw [intervalIntegral.integral_comp_add_left (fun s => M s) t, add_zero,
    intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable (μ := MeasureTheory.volume) _ _) (hc.intervalIntegrable (μ := MeasureTheory.volume) _ _)]
end GlobalTheory.ExponentialIntegralUnits
