-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellGeometry13_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:10:18.629436+00:00
-- url     : https://prove2.me/submissions/9d15a7e8-a046-4e63-a7d8-6a52f2c8a73e

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
lemma cellGeometry13_eu_oai (k : Fin 100) :
    0 ≤ cellMagnitude 13 k ∧ cellMagnitude 13 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 13 → 0 ≤ cellSeparation 13 k j ∧ cellSeparation 13 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 13 k ∧ cellMagnitude 13 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 13 → 0 ≤ cellSeparation 13 k j ∧ cellSeparation 13 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellGeometry13_eu_oai := @OAI.AtomicTriangular.Construction.cellGeometry13_eu_oai
