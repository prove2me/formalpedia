-- Prove2me | solution 1 for GlobalTheory.LaurentConst.constantCoeff_scaleP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:40:00.586284+00:00
-- url     : https://prove2.me/submissions/b966b0b2-918e-44ef-93bd-0c7754bec54e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentConst
open AddMonoidAlgebra
attribute [-simp] LaurentPolynomial.single_eq_C_mul_T
variable {L R : Type} [CommRing L] [CommRing R]
variable (r : L →+* R) (t : Rˣ)
namespace GlobalTheory.LaurentConst
theorem _root_.solution : PowerSeries.constantCoeff.comp (scaleP r t) =
    r.comp PowerSeries.constantCoeff := by
  refine RingHom.ext fun p ↦ ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, scaleP, RingHom.comp_apply,
    PowerSeries.coeff_rescale, PowerSeries.coeff_map, pow_zero, one_mul]
end GlobalTheory.LaurentConst
