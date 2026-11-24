-- Prove2me | solution 1 for GlobalTheory.LaurentConst.eq_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:55:42.844835+00:00
-- url     : https://prove2.me/submissions/e93e0f89-f31d-4dd2-8475-103fce5b5bd9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
import Theorems.Thm_GlobalTheory_LaurentConst_coeff_atZero
import Theorems.Thm_GlobalTheory_LaurentConst_coeff_atInf
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
namespace GlobalTheory.LaurentConst
theorem _root_.solution {z : AddMonoidAlgebra R ℤ} {p q : PowerSeries R}
    (hp : atZero R z = HahnSeries.ofPowerSeries ℤ R p)
    (hq : atInf R z = HahnSeries.ofPowerSeries ℤ R q) :
    z = algebraMap R _ (PowerSeries.constantCoeff p) := by
  ext n
  rcases lt_trichotomy n 0 with h | rfl | h
  · rw [← coeff_atZero, hp, PowerSeries.coeff_coe, if_pos h]
    simp [Finsupp.single_apply, h.ne]
  · rw [← coeff_atZero, hp, PowerSeries.coeff_coe]
    simp
  · rw [← coeff_atInf, hq, PowerSeries.coeff_coe, if_pos (by omega)]
    simp [Finsupp.single_apply, h.ne']
end GlobalTheory.LaurentConst
