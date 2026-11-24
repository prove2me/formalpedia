-- Prove2me | solution 1 for GlobalTheory.HeckeTheta.Decay.one_dim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:20:46.10179+00:00
-- url     : https://prove2.me/submissions/c6ff6f8c-c34e-45a8-858a-32aecdc28c24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableWeightedHeckeThetaKernelHalfSpace
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.HeckeTheta GlobalTheory.HeckeTheta.Decay
open GlobalTheory.HeckeTheta
variable {I : Type} [Fintype I]
namespace GlobalTheory.HeckeTheta.Decay
theorem _root_.solution {σ c R t : ℝ} (hc : 0 < c) (hR : 0 ≤ R) (ht : -R ≤ t) :
    σ * t - c * Real.exp t ≤ ((|σ| + 1) ^ 2 / (2 * c) + (|σ| + 1) * R) - |t| := by
  have hK1 : 0 ≤ (|σ| + 1) ^ 2 / (2 * c) := by positivity
  have hσ := abs_nonneg σ
  rcases le_total 0 t with h | h
  · have he : t ^ 2 / 2 ≤ Real.exp t := by
      have := Real.pow_div_factorial_le_exp t h 2
      simpa using this
    rw [abs_of_nonneg h]
    have hs : σ * t ≤ |σ| * t := mul_le_mul_of_nonneg_right (le_abs_self σ) h
    have key : (|σ| + 1) * t - c * (t ^ 2 / 2) ≤ (|σ| + 1) ^ 2 / (2 * c) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (c * t - (|σ| + 1))]
    nlinarith [mul_le_mul_of_nonneg_left he hc.le]
  · rw [abs_of_nonpos h]
    have hs : σ * t ≤ |σ| * R := by
      calc σ * t ≤ |σ * t| := le_abs_self _
        _ = |σ| * |t| := abs_mul _ _
        _ ≤ |σ| * R := mul_le_mul_of_nonneg_left (by rw [abs_of_nonpos h]; linarith) hσ
    have := mul_pos hc (Real.exp_pos t)
    nlinarith
end GlobalTheory.HeckeTheta.Decay
