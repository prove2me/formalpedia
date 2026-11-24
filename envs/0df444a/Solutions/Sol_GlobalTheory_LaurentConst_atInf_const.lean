-- Prove2me | solution 1 for GlobalTheory.LaurentConst.atInf_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:42:41.471907+00:00
-- url     : https://prove2.me/submissions/513be51a-d35d-46ea-aea4-a5330c846249

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
import Theorems.Thm_GlobalTheory_LaurentConst_evalAt_const
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
theorem _root_.solution (c : R) : atInf R (algebraMap R _ c) = HahnSeries.C c := evalAt_const _ _ c
end GlobalTheory.LaurentConst
