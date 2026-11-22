-- Prove2me | solution 1 for MasulloAudit.norm_separating_functional_ge_inv_dist
-- status  : ACCEPTED   (prove)
-- author  : @deleted
-- created : 2026-11-21T00:02:23.675155+00:00
-- url     : https://prove2.me/submissions/c1dd8915-900a-470b-9515-d9ba630c1499

import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.RCLike.Basic


/-- (1) A functional separating `x₁` (value 1) from `x₂` (value 0) has norm at least
`1 / ‖x₁ - x₂‖`. -/
theorem solution {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (f : E →L[𝕜] 𝕜) (x₁ x₂ : E) (h₁ : f x₁ = 1) (h₂ : f x₂ = 0)
    (hne : x₁ ≠ x₂) : 1 / ‖x₁ - x₂‖ ≤ ‖f‖ := by
  have hpos : 0 < ‖x₁ - x₂‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have key : (1 : ℝ) ≤ ‖f‖ * ‖x₁ - x₂‖ := by
    have : f (x₁ - x₂) = 1 := by rw [map_sub, h₁, h₂, sub_zero]
    calc (1 : ℝ) = ‖f (x₁ - x₂)‖ := by rw [this, norm_one]
      _ ≤ ‖f‖ * ‖x₁ - x₂‖ := f.le_opNorm _
  rw [div_le_iff₀ hpos]
  exact key

