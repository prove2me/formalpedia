-- Prove2me | solution 1 for GlobalTheory.ConvSeries.WeightedPowerFormIntegrability.pow_mul_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:44:29.886126+00:00
-- url     : https://prove2.me/submissions/76511511-3c11-4866-87ad-4732347eb247

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumGaussianConvolutionSeriesTermIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.ConvSeries GlobalTheory.ConvSeries.WeightedPowerFormIntegrability
open GlobalTheory.ConvSeries
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace GlobalTheory.ConvSeries.WeightedPowerFormIntegrability
theorem _root_.solution {β : ℝ} (hβ : 0 < β) (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ k * Real.exp (-(β * x ^ 2)) ≤
      k.factorial * Real.exp (1 / (2 * β)) * Real.exp (-(β / 2 * x ^ 2)) := by
  have h1 : x ^ k ≤ k.factorial * Real.exp x := by
    have := Real.pow_div_factorial_le_exp x hx k
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have h2 : x - β * x ^ 2 ≤ 1 / (2 * β) - β / 2 * x ^ 2 := by
    have ht : 1 / (2 * β) * (2 * β) = 1 := by field_simp
    nlinarith [sq_nonneg (β * x - 1)]
  calc x ^ k * Real.exp (-(β * x ^ 2)) ≤ (k.factorial * Real.exp x) * Real.exp (-(β * x ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = k.factorial * Real.exp (x - β * x ^ 2) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ k.factorial * Real.exp (1 / (2 * β) - β / 2 * x ^ 2) := by gcongr
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; ring_nf
end GlobalTheory.ConvSeries.WeightedPowerFormIntegrability
