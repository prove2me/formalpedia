-- Prove2me | solution 1 for GlobalTheory.LaurentConst.map_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:45.058871+00:00
-- url     : https://prove2.me/submissions/9734e739-04ae-4cfc-b20e-1bb2c1bfcd1d

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
variable {t}
namespace GlobalTheory.LaurentConst
theorem _root_.solution {A : Type} [CommRing A] [IsReduced A] (ht : IsNilpotent ((t : R) - 1))
    (ρ : R →+* A) : ρ t = 1 := by
  have := (ht.map ρ).eq_zero
  rwa [map_sub, map_one, sub_eq_zero] at this
end GlobalTheory.LaurentConst
