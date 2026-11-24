-- Prove2me | solution 1 for GlobalTheory.finite_twelve_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:00:16.752443+00:00
-- url     : https://prove2.me/submissions/411f19d7-8ef8-4d6e-bbc6-64e153a01072

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIntegralModelOfForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Theorems.Thm_GlobalTheory_finite_nsmul_eq_zero_mul
import Theorems.Thm_GlobalTheory_finite_two_torsion
import Theorems.Thm_GlobalTheory_finite_three_torsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine Polynomial NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {F : Type*} [Field F] {W : WeierstrassCurve F}
variable [CharZero F] [DecidableEq F]
namespace GlobalTheory
theorem _root_.solution : {P : W.toAffine.Point | 12 • P = 0}.Finite :=
  finite_nsmul_eq_zero_mul (m := 2 * 2) (n := 3)
    (finite_nsmul_eq_zero_mul finite_two_torsion finite_two_torsion) finite_three_torsion
end GlobalTheory
