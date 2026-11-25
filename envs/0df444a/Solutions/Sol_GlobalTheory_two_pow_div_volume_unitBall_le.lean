-- Prove2me | solution 1 for GlobalTheory.two_pow_div_volume_unitBall_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:06:13.30031+00:00
-- url     : https://prove2.me/submissions/3b78ff2e-a54d-483f-ab1f-d1b9c9eddff8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DiscreteTopologySpanOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Theorems.Thm_GlobalTheory_volume_real_unitBall_pos
import Theorems.Thm_GlobalTheory_two_div_sqrt_pow_le_volume_unitBall
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
noncomputable section
open Module Submodule MeasureTheory
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable (E)
namespace GlobalTheory
theorem _root_.solution :
    2 ^ finrank ℝ E / volume.real (Metric.ball (0 : E) 1) ≤
      (finrank ℝ E : ℝ) ^ ((finrank ℝ E : ℝ) / 2) := by
  have h := two_div_sqrt_pow_le_volume_unitBall E
  have h2 : (finrank ℝ E : ℝ) ^ ((finrank ℝ E : ℝ) / 2) = √(finrank ℝ E : ℝ) ^ finrank ℝ E := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    congr 1; ring
  have h3 : 0 < √(finrank ℝ E : ℝ) ^ finrank ℝ E := by
    rcases Nat.eq_zero_or_pos (finrank ℝ E) with h0 | hpos
    · simp [h0]
    · positivity
  rw [div_pow, div_le_iff₀ h3] at h
  rwa [h2, div_le_iff₀ volume_real_unitBall_pos, mul_comm]
end GlobalTheory
