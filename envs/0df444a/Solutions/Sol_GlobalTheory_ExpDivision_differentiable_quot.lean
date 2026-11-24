-- Prove2me | solution 1 for GlobalTheory.ExpDivision.differentiable_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:44:36.46119+00:00
-- url     : https://prove2.me/submissions/1f60caac-9f83-423d-b4bc-65dcf0e8304f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityAsSumExpMinusOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.ExpDivision
namespace GlobalTheory.ExpDivision
theorem _root_.solution (a : ℝ) : Differentiable ℂ (quot a) := by
  rw [← differentiableOn_univ, quot, Complex.differentiableOn_dslope Filter.univ_mem]
  fun_prop
end GlobalTheory.ExpDivision
