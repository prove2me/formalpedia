-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellGeometry23_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:11:44.993195+00:00
-- url     : https://prove2.me/submissions/7c300c3a-3f22-453c-a876-452ac60aa333

import Mathlib
import Definitions.Def_OAIQ334E011

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_SineGrid2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellGeometry23_eu_oai (k : Fin 100) :
    0 ≤ cellMagnitude 23 k ∧ cellMagnitude 23 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 23 → 0 ≤ cellSeparation 23 k j ∧ cellSeparation 23 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 23 k ∧ cellMagnitude 23 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 23 → 0 ≤ cellSeparation 23 k j ∧ cellSeparation 23 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellGeometry23_eu_oai := @OAI.AtomicTriangular.Construction.cellGeometry23_eu_oai
