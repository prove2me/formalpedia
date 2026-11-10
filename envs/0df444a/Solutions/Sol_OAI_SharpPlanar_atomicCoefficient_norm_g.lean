-- Prove2me | solution 1 for OAI.SharpPlanar.atomicCoefficient_norm_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:19:47.823921+00:00
-- url     : https://prove2.me/submissions/1f74da37-02d9-4ed7-9285-dca0ba9c3437

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G362
import Theorems.Thm_OAI_SharpPlanar_Pcoeff_norm_g

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

lemma atomicCoefficient_norm_g_oai (j : Fin 7) : ‖atomicCoefficient j‖ = atomMass j := by
  fin_cases j <;> (first | (simp [atomicCoefficient,atomMass,norm_mul,Pcoeff_norm_g,coeffMass]; all_goals first | (norm_num [atomicCoefficient,atomMass,norm_mul,Pcoeff_norm_g,coeffMass]; done) | rfl | decide) | (norm_num [atomicCoefficient,atomMass,norm_mul,Pcoeff_norm_g,coeffMass]; done) | norm_num [atomicCoefficient,atomMass,norm_mul,Pcoeff_norm_g,coeffMass])

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.atomicCoefficient_norm_g_oai := @OAI.SharpPlanar.atomicCoefficient_norm_g_oai
