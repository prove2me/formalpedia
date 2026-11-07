-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.density_finite_check_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T00:44:49.157618+00:00
-- url     : https://prove2.me/submissions/9e90dfb8-5cc2-47a3-a944-0410e45b5971

import Mathlib
import Definitions.Def_OAIQ098E126

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

lemma density_finite_check_e_oai (n : Fin 12) (hn : n.val ∈ residues) (j : Fin 6) : DensityCheck n.val j := by
  fin_cases n <;> simp only [residues,Finset.mem_insert,Finset.mem_singleton] at hn
  all_goals first | omega | (fin_cases j <;> decide +kernel)

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.density_finite_check_e_oai := @OAI.SharpPlanar.IntegerBasis.density_finite_check_e_oai
