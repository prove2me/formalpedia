-- Prove2me | solution 1 for ModularCurve.arithmeticGalois_smul_coeffEmb
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/4246d812-100c-5e5a-8fa7-865216bbd24e

import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_arithmeticGalois_smul_coeffEmb

open ModularCurve AlgebraicCurve IntermediateField HahnSeries

theorem solution {L : Type*} [Field L] [Algebra ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (σ : L ≃ₐ[ℚ] L) {x : LaurentSeries ℚ} (hx : x ∈ F₀) : ModularCurve.arithmeticGalois F₀ σ • (⟨ModularCurve.coeffEmb L x, ModularCurve.coeffEmb_mem_laurentBaseChange L hx⟩ : ModularCurve.laurentBaseChange L F₀) = ⟨ModularCurve.coeffEmb L x, ModularCurve.coeffEmb_mem_laurentBaseChange L hx⟩ :=
  by
  apply Subtype.ext
  rw [coe_arithmeticGalois_smul]
  exact coeffMap_coeffEmb σ x

end S_ModularCurve_arithmeticGalois_smul_coeffEmb
end P2MW
export P2MW.S_ModularCurve_arithmeticGalois_smul_coeffEmb (solution)
