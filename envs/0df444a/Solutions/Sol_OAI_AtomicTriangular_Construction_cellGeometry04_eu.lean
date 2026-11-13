-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellGeometry04_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:08:56.883304+00:00
-- url     : https://prove2.me/submissions/86630a09-c2bd-4581-a203-1a0c2c8c3405

import Mathlib
import Definitions.Def_OAIQ334E011

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_SineGrid0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellGeometry04_eu_oai (k : Fin 100) :
    0 ≤ cellMagnitude 4 k ∧ cellMagnitude 4 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 4 → 0 ≤ cellSeparation 4 k j ∧ cellSeparation 4 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 4 k ∧ cellMagnitude 4 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 4 → 0 ≤ cellSeparation 4 k j ∧ cellSeparation 4 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellGeometry04_eu_oai := @OAI.AtomicTriangular.Construction.cellGeometry04_eu_oai
