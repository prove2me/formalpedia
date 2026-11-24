-- Prove2me | solution 1 for GlobalTheory.LaurentConst.comp_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:39:58.905504+00:00
-- url     : https://prove2.me/submissions/4e2d56a5-23c2-42eb-a61f-5acbfea4627e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
import Theorems.Thm_GlobalTheory_LaurentConst_hom_ext
import Theorems.Thm_GlobalTheory_LaurentConst_scale_single_zero
import Theorems.Thm_GlobalTheory_LaurentConst_scale_single_one
import Theorems.Thm_GlobalTheory_LaurentConst_map_eq_one
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
variable {t}
namespace GlobalTheory.LaurentConst
theorem _root_.solution {A : Type} [CommRing A] [IsReduced A] (ht : IsNilpotent ((t : R) - 1))
    (ρ : AddMonoidAlgebra R ℤ →+* A) : ρ.comp (scale r t) = ρ.comp (scale r 1) := by
  refine hom_ext (fun c ↦ by simp only [RingHom.comp_apply, scale_single_zero]) ?_
  have e : (single 1 (t : R) : AddMonoidAlgebra R ℤ) = algebraMap R _ t * single 1 1 := by
    simp [single_mul_single]
  simp only [RingHom.comp_apply, scale_single_one, Units.val_one]
  rw [e, map_mul, ← RingHom.comp_apply, map_eq_one ht, one_mul]
end GlobalTheory.LaurentConst
