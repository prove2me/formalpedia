-- Prove2me | solution 1 for GlobalTheory.LaurentConst.scaleL_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:27:02.949418+00:00
-- url     : https://prove2.me/submissions/ce797fd5-5d41-47f2-94db-a1b2997c3e95

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
theorem _root_.solution (p : PowerSeries L) : scaleL r t (HahnSeries.ofPowerSeries ℤ L p) =
    HahnSeries.ofPowerSeries ℤ R (scaleP r t p) :=
  IsLocalization.Away.lift_eq _ _ p
end GlobalTheory.LaurentConst
