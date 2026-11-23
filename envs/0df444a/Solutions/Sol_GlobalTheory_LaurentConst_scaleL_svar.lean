-- Prove2me | solution 1 for GlobalTheory.LaurentConst.scaleL_svar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:24.456391+00:00
-- url     : https://prove2.me/submissions/bd8bd6a3-ba76-4775-bbf6-069e1b0e0ff5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
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
theorem _root_.solution : scaleL r t (svar L : LaurentSeries L) =
    HahnSeries.C (t : R) * (svar R : LaurentSeries R) := by
  rw [← coe_scaleP_X r, ← scaleL_coe, HahnSeries.ofPowerSeries_X]; rfl
end GlobalTheory.LaurentConst
