-- Prove2me | solution 1 for ModularCurve.arithmeticGalois_smul_eq_self_of_forall_coeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/df953bcb-3c06-5f2c-9677-3c203f4094c9

import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_arithmeticGalois_smul_eq_self_of_forall_coeff_eq

set_option autoImplicit false

open ModularCurve

theorem solution
    {L : Type*} [Field L] [Algebra ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (σ : L ≃ₐ[ℚ] L) (z : laurentBaseChange L F₀)
    (hz : ∀ n : ℤ, σ (((z : laurentBaseChange L F₀) : LaurentSeries L).coeff n) = ((z : laurentBaseChange L F₀) : LaurentSeries L).coeff n) :
    arithmeticGalois F₀ σ • z = z := by
  apply Subtype.ext
  rw [coe_arithmeticGalois_smul]
  ext n
  rw [coeffMap_coeff]
  exact hz n

end S_ModularCurve_arithmeticGalois_smul_eq_self_of_forall_coeff_eq
end P2MW
export P2MW.S_ModularCurve_arithmeticGalois_smul_eq_self_of_forall_coeff_eq (solution)
