-- Prove2me | solution 1 for GlobalTheory.LaurentConst.svar_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:25.723515+00:00
-- url     : https://prove2.me/submissions/43085459-088b-4517-b6ac-951a06a85a09

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
namespace GlobalTheory.LaurentConst
theorem _root_.solution (n : ℤ) : ((svar R ^ n : (LaurentSeries R)ˣ) : LaurentSeries R) =
    HahnSeries.single n 1 := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih => rw [zpow_add_one, Units.val_mul, ih]; simp [svar, HahnSeries.single_mul_single]
  | pred n ih =>
    rw [zpow_sub_one, Units.val_mul, ih]; simp [svar, HahnSeries.single_mul_single, sub_eq_add_neg]
end GlobalTheory.LaurentConst
