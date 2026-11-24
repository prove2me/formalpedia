-- Prove2me | solution 1 for GlobalTheory.HeckeTheta.Decay.pow_mul_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:20:32.156536+00:00
-- url     : https://prove2.me/submissions/cc4dd90c-277b-40fa-b671-dc69a000e18a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableWeightedHeckeThetaKernelHalfSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.HeckeTheta GlobalTheory.HeckeTheta.Decay
open GlobalTheory.HeckeTheta
namespace GlobalTheory.HeckeTheta.Decay
theorem _root_.solution (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ k * Real.exp (-2 * Real.pi * x ^ 2) ≤ (1 + (k.factorial : ℝ)) * Real.exp (-Real.pi * x ^ 2) := by
  have h1 : x ^ k ≤ 1 + (x ^ 2) ^ k := by
    rcases le_total x 1 with h | h
    · have := pow_le_one₀ (n := k) hx h
      have := pow_nonneg (sq_nonneg x) k
      linarith
    · have h' : x ^ k ≤ x ^ (2 * k) := pow_le_pow_right₀ h (by omega)
      rw [pow_mul] at h'
      linarith
  have h2 : (x ^ 2) ^ k ≤ (k.factorial : ℝ) * Real.exp (x ^ 2) := by
    have := Real.pow_div_factorial_le_exp (x ^ 2) (sq_nonneg x) k
    have hf : (0:ℝ) < k.factorial := by positivity
    rwa [div_le_iff₀ hf, mul_comm] at this
  have he := Real.exp_pos (-2 * Real.pi * x ^ 2)
  have h3 : Real.exp (x ^ 2) * Real.exp (-2 * Real.pi * x ^ 2) ≤ Real.exp (-Real.pi * x ^ 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three, sq_nonneg x])
  have h4 : Real.exp (-2 * Real.pi * x ^ 2) ≤ Real.exp (-Real.pi * x ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, sq_nonneg x])
  have hf0 : (0:ℝ) ≤ k.factorial := by positivity
  calc x ^ k * Real.exp (-2 * Real.pi * x ^ 2)
      ≤ (1 + (x ^ 2) ^ k) * Real.exp (-2 * Real.pi * x ^ 2) := mul_le_mul_of_nonneg_right h1 he.le
    _ = Real.exp (-2 * Real.pi * x ^ 2) + (x ^ 2) ^ k * Real.exp (-2 * Real.pi * x ^ 2) := by ring
    _ ≤ Real.exp (-Real.pi * x ^ 2) + (k.factorial : ℝ) * (Real.exp (x ^ 2) * Real.exp (-2 * Real.pi * x ^ 2)) := by
        have : (x ^ 2) ^ k * Real.exp (-2 * Real.pi * x ^ 2)
            ≤ ((k.factorial : ℝ) * Real.exp (x ^ 2)) * Real.exp (-2 * Real.pi * x ^ 2) :=
          mul_le_mul_of_nonneg_right h2 he.le
        linarith
    _ ≤ Real.exp (-Real.pi * x ^ 2) + (k.factorial : ℝ) * Real.exp (-Real.pi * x ^ 2) := by
        have := mul_le_mul_of_nonneg_left h3 hf0
        linarith
    _ = _ := by ring
end GlobalTheory.HeckeTheta.Decay
