-- Prove2me | solution 1 for GlobalTheory.LaurentConst.comp_scaleP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:39:59.726034+00:00
-- url     : https://prove2.me/submissions/233530a4-73ba-4125-8cb2-41ea03fc3fa1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
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
    (ρ : PowerSeries R →+* A) : ρ.comp (scaleP r t) = ρ.comp (scaleP r 1) := by
  refine RingHom.ext fun p ↦ ?_
  choose c hc using fun n : ℕ ↦ sub_one_dvd_pow_sub_one (t : R) n
  have e : scaleP r t p = scaleP r 1 p +
      (PowerSeries.C (t : R) - 1) * PowerSeries.mk fun n ↦ c n * r (PowerSeries.coeff n p) := by
    ext n
    rw [← map_one PowerSeries.C, ← map_sub]
    simp only [scaleP, RingHom.comp_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_map,
      map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, Units.val_one, one_pow]
    linear_combination (r (PowerSeries.coeff n p)) * hc n
  have h1 : ρ (PowerSeries.C (t : R)) = 1 := map_eq_one ht (ρ.comp PowerSeries.C)
  simp only [RingHom.comp_apply]
  rw [e, map_add, map_mul, map_sub, h1, map_one, sub_self, zero_mul, add_zero]
end GlobalTheory.LaurentConst
