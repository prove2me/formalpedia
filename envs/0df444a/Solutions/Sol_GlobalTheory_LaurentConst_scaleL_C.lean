-- Prove2me | solution 1 for GlobalTheory.LaurentConst.scaleL_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:24.13397+00:00
-- url     : https://prove2.me/submissions/a3b1c1f4-f3a8-46ee-ad08-6c6e6e8f8c94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
import Theorems.Thm_GlobalTheory_LaurentConst_scaleP_C
import Theorems.Thm_GlobalTheory_LaurentConst_scaleL_coe
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
theorem _root_.solution (c : L) : scaleL r t (HahnSeries.C c) = HahnSeries.C (r c) := by
  rw [← HahnSeries.ofPowerSeries_C, scaleL_coe, scaleP_C, HahnSeries.ofPowerSeries_C]
end GlobalTheory.LaurentConst
