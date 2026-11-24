-- Prove2me | solution 1 for GlobalTheory.LaurentConst.coeff_atInf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:39:56.78339+00:00
-- url     : https://prove2.me/submissions/d45b408c-a0d1-4698-b5b3-4339f458e965

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
import Theorems.Thm_GlobalTheory_LaurentConst_evalAt_single
import Theorems.Thm_GlobalTheory_LaurentConst_svar_zpow
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
theorem _root_.solution (z : AddMonoidAlgebra R ℤ) (n : ℤ) : (atInf R z).coeff (-n) = z.coeff n := by
  induction z using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single m r =>
    rw [atInf, evalAt_single, inv_zpow', svar_zpow]
    simp [HahnSeries.coeff_single, Finsupp.single_apply, eq_comm]
end GlobalTheory.LaurentConst
