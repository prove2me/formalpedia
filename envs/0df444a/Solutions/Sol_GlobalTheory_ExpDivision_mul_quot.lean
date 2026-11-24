-- Prove2me | solution 1 for GlobalTheory.ExpDivision.mul_quot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:49.693363+00:00
-- url     : https://prove2.me/submissions/a7b96293-cbd2-4f42-9210-4f261fb1a3a1

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
theorem _root_.solution (a : ℝ) (z : ℂ) : z * quot a z = Complex.exp (Complex.I * (a * z)) - 1 := by
  have := sub_smul_dslope (fun z : ℂ => Complex.exp (Complex.I * (a * z))) 0 z
  simpa [quot] using this
end GlobalTheory.ExpDivision
