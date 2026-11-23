-- Prove2me | solution 1 for GlobalTheory.PerronKernel.norm_le_three
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:04.926315+00:00
-- url     : https://prove2.me/submissions/14980ef9-c2fd-458c-a3e7-7098a73c0402

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.PerronKernel
namespace GlobalTheory.PerronKernel
theorem _root_.solution {x p q r : ℂ} (h : I * x = p - q + I * r ∨ I * x = q - p + I * r) :
    ‖x‖ ≤ ‖p‖ + ‖q‖ + ‖r‖ := by
  have hx : ‖x‖ = ‖I * x‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have hr : ‖I * r‖ = ‖r‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  rcases h with h | h
  · rw [hx, h]
    calc ‖p - q + I * r‖ ≤ ‖p - q‖ + ‖I * r‖ := norm_add_le _ _
      _ ≤ ‖p‖ + ‖q‖ + ‖r‖ := by rw [hr]; linarith [norm_sub_le p q]
  · rw [hx, h]
    calc ‖q - p + I * r‖ ≤ ‖q - p‖ + ‖I * r‖ := norm_add_le _ _
      _ ≤ ‖p‖ + ‖q‖ + ‖r‖ := by rw [hr]; linarith [norm_sub_le q p]
end GlobalTheory.PerronKernel
