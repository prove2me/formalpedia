-- Prove2me | solution 1 for GlobalTheory.Hk.integral_mul_exp_neg_Ioi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:35:02.250423+00:00
-- url     : https://prove2.me/submissions/25da25cb-77a4-4e16-bdf6-583792286087

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
theorem _root_.solution {t : ℝ} (ht : 0 < t) (y : ℝ) :
    IntegrableOn (fun x : ℝ => t * Real.exp (-(t * x))) (Set.Ioi y) ∧
    ∫ x in Set.Ioi y, t * Real.exp (-(t * x)) = Real.exp (-(t * y)) := by
  have h1 := exp_neg_integrableOn_Ioi y ht
  have h2 := integral_exp_mul_Ioi (a := -t) (by linarith) y
  simp only [neg_mul] at h1 h2
  refine ⟨h1.const_mul t, ?_⟩
  rw [integral_const_mul, h2]
  field_simp
end GlobalTheory.Hk
