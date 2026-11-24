-- Prove2me | solution 1 for GlobalTheory.FibLine.Intg.continuous_lineVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:51:52.164343+00:00
-- url     : https://prove2.me/submissions/bdc66a76-ac2a-42a3-8203-181f2e544fbe

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
theorem _root_.solution (a : Fin 2) : Continuous fun x : ℂ => lineVec x a := by
  fin_cases a
  · simpa [lineVec] using continuous_const
  · simpa [lineVec] using continuous_id'
end GlobalTheory.FibLine.Intg
