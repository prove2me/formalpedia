-- Prove2me | solution 1 for GlobalTheory.FibLine.Intg.integrable_fsDens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:51:54.011573+00:00
-- url     : https://prove2.me/submissions/ad451a5a-d3c5-46ba-b54a-c1dab7159f32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableProdQCoefMulFsDens

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial GlobalTheory.FibLine
open GlobalTheory GlobalTheory.FibLine GlobalTheory.FibLine.Intg
namespace GlobalTheory.FibLine.Intg
theorem _root_.solution : Integrable fsDens := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 4)
    (by rw [Complex.finrank_real_complex]; norm_num)
  refine (h.const_mul (1 / Real.pi)).congr (Filter.Eventually.of_forall fun x => ?_)
  have hx : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  have e : (-4 / 2 : ℝ) = -((2 : ℕ) : ℝ) := by norm_num
  simp only [fsDens]
  rw [e, Real.rpow_neg hx.le, Real.rpow_natCast]
  have := Real.pi_pos
  field_simp
end GlobalTheory.FibLine.Intg
