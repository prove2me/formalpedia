-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellFactors11_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:05:44.439733+00:00
-- url     : https://prove2.me/submissions/94525eae-1df5-4796-b7d1-0c8d53bf767f

import Mathlib
import Definitions.Def_OAIQ334E011

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_SineGrid1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors11_eu_oai (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 11 k j) ∧ cellBarrier 11 < ∏ j : Fin 15,(cellFactor 11 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 11 k j) ∧ cellBarrier 11 < ∏ j : Fin 15,(cellFactor 11 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellFactors11_eu_oai := @OAI.AtomicTriangular.Construction.cellFactors11_eu_oai
