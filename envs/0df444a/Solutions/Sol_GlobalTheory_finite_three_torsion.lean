-- Prove2me | solution 1 for GlobalTheory.finite_three_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:50:02.985125+00:00
-- url     : https://prove2.me/submissions/a371953b-a1bb-46f2-8f9c-df191fb6c70d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIntegralModelOfForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Theorems.Thm_GlobalTheory_finite_points_of_root
import Theorems.Thm_GlobalTheory_three_nsmul_eq_zero_iff


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
theorem _root_.solution : {P : W.toAffine.Point | 3 • P = 0}.Finite :=
  finite_points_of_root (W.Ψ₃_ne_zero three_ne_zero) fun _ _ h hP =>
    (three_nsmul_eq_zero_iff h).mp hP
end GlobalTheory
