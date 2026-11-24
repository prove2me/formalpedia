-- Prove2me | solution 1 for GlobalTheory.ExpDivision.quot_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:53.476138+00:00
-- url     : https://prove2.me/submissions/3e289975-338a-4185-942f-101fe9105e7b

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
theorem _root_.solution (a : ℝ) : quot a 0 = Complex.I * a := by
  have h : HasDerivAt (fun z : ℂ => Complex.exp (Complex.I * (a * z)))
      (Complex.exp (Complex.I * (a * 0)) * (Complex.I * (a * 1))) 0 :=
    (((hasDerivAt_id (0 : ℂ)).const_mul (a : ℂ)).const_mul Complex.I).cexp
  rw [quot, dslope_same, h.deriv]; simp
end GlobalTheory.ExpDivision
