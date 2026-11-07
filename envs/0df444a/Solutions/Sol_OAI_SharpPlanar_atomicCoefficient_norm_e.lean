-- Prove2me | solution 1 for OAI.SharpPlanar.atomicCoefficient_norm_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T19:42:53.919875+00:00
-- url     : https://prove2.me/submissions/da144003-217d-4462-902d-288e47664107

import Mathlib
import Definitions.Def_OAIQ098E125
import Theorems.Thm_OAI_SharpPlanar_Pcoeff_norm_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar
open IntegerBasis

lemma atomicCoefficient_norm_e_oai (j : Fin 7) : ‖atomicCoefficient j‖ = atomMass j := by
  fin_cases j <;> (first | (simp [atomicCoefficient,atomMass,norm_mul,Pcoeff_norm_e,coeffMass]; all_goals first | (norm_num [atomicCoefficient,atomMass,norm_mul,Pcoeff_norm_e,coeffMass]; done) | rfl | decide) | (norm_num [atomicCoefficient,atomMass,norm_mul,Pcoeff_norm_e,coeffMass]; done) | norm_num [atomicCoefficient,atomMass,norm_mul,Pcoeff_norm_e,coeffMass])

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.atomicCoefficient_norm_e_oai := @OAI.SharpPlanar.atomicCoefficient_norm_e_oai
