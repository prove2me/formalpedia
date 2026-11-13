-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellFactors18_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:06:43.776207+00:00
-- url     : https://prove2.me/submissions/2d51ba89-8d26-4f0a-95ad-2efdb3d20f0d

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
lemma cellFactors18_eu_oai (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 18 k j) ∧ cellBarrier 18 < ∏ j : Fin 15,(cellFactor 18 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 18 k j) ∧ cellBarrier 18 < ∏ j : Fin 15,(cellFactor 18 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellFactors18_eu_oai := @OAI.AtomicTriangular.Construction.cellFactors18_eu_oai
