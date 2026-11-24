-- Prove2me | solution 1 for GlobalTheory.Hk.integral_mul_exp_neg_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:35:03.136305+00:00
-- url     : https://prove2.me/submissions/45f98882-8c06-4a9b-816f-715fa20e8743

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk
namespace GlobalTheory.Hk
theorem _root_.solution {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-(t * x))) (Set.Ioi 0) ∧
    ∫ t in Set.Ioi 0, t * Real.exp (-(t * x)) = x ^ (-2 : ℝ) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := x) (by norm_num) hx
  have h2 : ∫ t in Set.Ioi 0, t * Real.exp (-(t * x)) = x ^ (-2 : ℝ) := by
    have e : (2 : ℝ) - 1 = 1 := by norm_num
    simp only [e, Real.rpow_one, Real.Gamma_two, mul_one] at h
    simp only [mul_comm _ x]
    rw [h, Real.rpow_neg hx.le, one_div, Real.inv_rpow hx.le]
  refine ⟨Integrable.of_integral_ne_zero ?_, h2⟩
  rw [h2]
  positivity
end GlobalTheory.Hk
