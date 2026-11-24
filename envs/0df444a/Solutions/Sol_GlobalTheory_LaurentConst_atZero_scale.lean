-- Prove2me | solution 1 for GlobalTheory.LaurentConst.atZero_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:42:43.802546+00:00
-- url     : https://prove2.me/submissions/666dbc2f-2678-4034-b2e0-e0c143d79384

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
import Theorems.Thm_GlobalTheory_LaurentConst_evalAt_single
import Theorems.Thm_GlobalTheory_LaurentConst_hom_ext
import Theorems.Thm_GlobalTheory_LaurentConst_scaleL_C
import Theorems.Thm_GlobalTheory_LaurentConst_scaleL_svar
import Theorems.Thm_GlobalTheory_LaurentConst_scale_single_zero
import Theorems.Thm_GlobalTheory_LaurentConst_scale_single_one
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
theorem _root_.solution : (atZero R).comp (scale r t) = (scaleL r t).comp (atZero L) := by
  refine hom_ext (fun c ↦ ?_) ?_
  · simp only [RingHom.comp_apply, scale_single_zero, atZero, evalAt_single, zpow_zero,
      Units.val_one, mul_one, scaleL_C]
  · simp only [RingHom.comp_apply, scale_single_one, atZero, evalAt_single, zpow_one, map_one,
      one_mul, scaleL_svar]
end GlobalTheory.LaurentConst
