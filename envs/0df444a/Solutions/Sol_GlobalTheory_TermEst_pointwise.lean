-- Prove2me | solution 1 for GlobalTheory.TermEst.pointwise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:28:48.760583+00:00
-- url     : https://prove2.me/submissions/4491a3e9-c50f-4e05-b72c-90b5ac81792e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianConvolutionSeriesCoefficientDescFactoria

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.TermEst
namespace GlobalTheory.TermEst
theorem _root_.solution (b c θ α s t H : ℝ) (hc : 0 < c) (hθ : 1 ≤ θ) (hα : 0 < α)
    (hk : c * θ ^ 2 ≤ α * (b + c)) (hs : 0 ≤ s) (ht : 0 ≤ t) (hH : 0 ≤ H) (i m : ℕ) :
    (2 * c) ^ (i + m) / (m.factorial : ℝ) * t ^ m * (Real.exp (-((b + c) * s ^ 2)) * H * s ^ (i + m)) ≤
      θ⁻¹ ^ m * Real.exp (c * α * t ^ 2) * ((2 * c * s) ^ i * H) := by
  have hθ0 : 0 < θ := by linarith
  have e1 : (2 * c * θ * s * t) ^ m / (m.factorial : ℝ) ≤ Real.exp (2 * c * θ * s * t) :=
    Real.pow_div_factorial_le_exp _ (by positivity) m
  have e2 : 2 * c * θ * s * t ≤ c * α * t ^ 2 + (b + c) * s ^ 2 := by
    have q1 : 0 ≤ c * (α * t - θ * s) ^ 2 := by positivity
    have q2 : c * θ ^ 2 * s ^ 2 ≤ α * (b + c) * s ^ 2 := by
      exact mul_le_mul_of_nonneg_right hk (by positivity)
    have q3 : α * (2 * c * θ * s * t) ≤ α * (c * α * t ^ 2 + (b + c) * s ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left q3 hα
  have e3 : Real.exp (-((b + c) * s ^ 2)) * Real.exp (2 * c * θ * s * t) ≤ Real.exp (c * α * t ^ 2) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have hm : (0 : ℝ) < m.factorial := by positivity
  calc (2 * c) ^ (i + m) / (m.factorial : ℝ) * t ^ m * (Real.exp (-((b + c) * s ^ 2)) * H * s ^ (i + m))
      = ((2 * c * s) ^ i * H * θ⁻¹ ^ m) *
          (Real.exp (-((b + c) * s ^ 2)) * ((2 * c * θ * s * t) ^ m / (m.factorial : ℝ))) := by
        rw [inv_pow]; field_simp; ring
    _ ≤ ((2 * c * s) ^ i * H * θ⁻¹ ^ m) *
          (Real.exp (-((b + c) * s ^ 2)) * Real.exp (2 * c * θ * s * t)) := by gcongr
    _ ≤ ((2 * c * s) ^ i * H * θ⁻¹ ^ m) * Real.exp (c * α * t ^ 2) := by gcongr
    _ = θ⁻¹ ^ m * Real.exp (c * α * t ^ 2) * ((2 * c * s) ^ i * H) := by ring
end GlobalTheory.TermEst
