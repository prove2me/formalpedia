-- Prove2me | solution 1 for GlobalTheory.JR.integral_eq_zero_of_shift_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:19:58.551832+00:00
-- url     : https://prove2.me/submissions/c5bdcef0-4555-405f-99d9-ab98d3f459b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HasCompactSupportPartialFourierGLBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR
namespace GlobalTheory.JR
theorem _root_.solution {V : Type} [AddGroup V] [MeasurableSpace V] [MeasurableAdd V]
    (μ : Measure V) [μ.IsAddRightInvariant] (g : V → ℂ) (t : V) (z : ℂ) (hz : z ≠ 1)
    (h : ∀ x, g (x + t) = g x * z) : ∫ x, g x ∂μ = 0 := by
  have h1 : ∫ x, g x ∂μ = (∫ x, g x ∂μ) * z := by
    calc ∫ x, g x ∂μ = ∫ x, g (x + t) ∂μ := (integral_add_right_eq_self g t).symm
      _ = ∫ x, g x * z ∂μ := by simp only [h]
      _ = (∫ x, g x ∂μ) * z := integral_mul_const z g
  have h2 : (∫ x, g x ∂μ) * (1 - z) = 0 := by rw [mul_sub, mul_one, ← h1, sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact h3
  · exact absurd (sub_eq_zero.1 h3).symm hz
end GlobalTheory.JR
