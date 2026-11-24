-- Prove2me | solution 1 for GlobalTheory.mul_sqrt_le_of_weights
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:22:34.185801+00:00
-- url     : https://prove2.me/submissions/8b6b19c2-f6b2-4e9f-a191-1660ad4cbff5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_WeightedSumDriftInequality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (x e₁ e₂ ε u v M : ℝ) (hx : 0 ≤ x) (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂)
    (hε : 0 ≤ ε) (hu : 0 ≤ u) (hv : 0 ≤ v) (h : x ^ 2 ≤ ε ^ 2 * (e₁ * e₂))
    (h₁ : e₁ * u ≤ M) (h₂ : e₂ * v ≤ M) : x * Real.sqrt (u * v) ≤ ε * M := by
  have hM : 0 ≤ M := le_trans (mul_nonneg he₁ hu) h₁
  have hs0 := Real.sqrt_nonneg (u * v)
  have k3 : (x * Real.sqrt (u * v)) ^ 2 ≤ (ε * M) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hu hv)]
    calc x ^ 2 * (u * v) ≤ ε ^ 2 * (e₁ * e₂) * (u * v) :=
          mul_le_mul_of_nonneg_right h (mul_nonneg hu hv)
      _ = ε ^ 2 * ((e₁ * u) * (e₂ * v)) := by ring
      _ ≤ ε ^ 2 * (M * M) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h₁ h₂ (mul_nonneg he₂ hv) hM) (sq_nonneg ε)
      _ = (ε * M) ^ 2 := by ring
  nlinarith [mul_nonneg hx hs0, mul_nonneg hε hM]
end GlobalTheory
