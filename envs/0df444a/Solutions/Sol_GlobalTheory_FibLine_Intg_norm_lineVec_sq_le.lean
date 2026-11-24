-- Prove2me | solution 1 for GlobalTheory.FibLine.Intg.norm_lineVec_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:51:08.464053+00:00
-- url     : https://prove2.me/submissions/0cec341c-783a-4356-ae8c-dad709f7dcf9

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
theorem _root_.solution (x : ℂ) (a : Fin 2) : ‖lineVec x a‖ ^ 2 ≤ 1 + ‖x‖ ^ 2 := by
  fin_cases a
  · simp [lineVec]
  · simp [lineVec]
end GlobalTheory.FibLine.Intg
