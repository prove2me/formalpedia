-- Prove2me | solution 1 for ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/f88ecca3-cde0-5114-8f3b-2bff82a672ab

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange

set_option autoImplicit false

theorem solution
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) :
    FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := by
  subst hK
  obtain ⟨x, -, hfin⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange L Γ hT
  haveI := hfin
  have hce : ModularCurve.coeffEmb L ModularCurve.jq = ModularCurve.jqModC L := by
    rw [← ModularCurve.jqModC_rat]
    exact ModularCurve.map_jqModC (algebraMap ℚ L)
  have hjL : Transcendental L ((j : LaurentSeries L)) := by
    rw [hj, hce]
    exact ModularCurve.transcendental_jqModC L
  have hjt : Transcendental L j := fun h => hjL (IntermediateField.isAlgebraic_iff.mp h)
  exact AlgebraicCurve.finiteDimensional_adjoin_of_transcendental x hjt

end S_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
end P2MW
export P2MW.S_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange (solution)
