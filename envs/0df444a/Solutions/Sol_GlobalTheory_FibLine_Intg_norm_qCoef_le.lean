-- Prove2me | solution 1 for GlobalTheory.FibLine.Intg.norm_qCoef_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:11:53.069624+00:00
-- url     : https://prove2.me/submissions/2b9d5f23-7075-4eb7-9226-f820ee8dc7c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableProdQCoefMulFsDens
import Theorems.Thm_GlobalTheory_FibLine_Intg_norm_lineVec_sq_le

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
theorem _root_.solution (x : ℂ) (ab : Fin 2 × Fin 2) : ‖qCoef x ab‖ ≤ 1 := by
  have hx : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  unfold qCoef
  rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hx.le, div_le_one hx]
  have h1 := norm_lineVec_sq_le x ab.1
  have h2 := norm_lineVec_sq_le x ab.2
  nlinarith [sq_nonneg (‖lineVec x ab.2‖ - ‖lineVec x ab.1‖)]
end GlobalTheory.FibLine.Intg
