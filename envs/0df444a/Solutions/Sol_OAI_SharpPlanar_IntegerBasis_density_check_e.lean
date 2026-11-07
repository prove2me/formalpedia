-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.density_check_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T00:44:48.020668+00:00
-- url     : https://prove2.me/submissions/4593918e-767e-457e-bdde-d943a215075f

import Mathlib
import Definitions.Def_OAIQ098E126
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_density_finite_check_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar.IntegerBasis
open IntegerIntervals IntegerAlpha

lemma density_check_e_oai (n : ℕ) (hn : n%12 ∈ residues) (j : Fin 6) : DensityCheck n j := by
  have hc := density_finite_check_e ⟨n%12,by omega⟩ hn j
  simpa only [DensityCheck,aLookup,bLookup,Nat.mod_mod] using hc

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.density_check_e_oai := @OAI.SharpPlanar.IntegerBasis.density_check_e_oai
