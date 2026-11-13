-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellGeometry10_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:09:49.432204+00:00
-- url     : https://prove2.me/submissions/4e4f037d-ebf0-4baa-a95e-6f0d2976f776

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
lemma cellGeometry10_eu_oai (k : Fin 100) :
    0 ≤ cellMagnitude 10 k ∧ cellMagnitude 10 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 10 → 0 ≤ cellSeparation 10 k j ∧ cellSeparation 10 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 10 k ∧ cellMagnitude 10 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 10 → 0 ≤ cellSeparation 10 k j ∧ cellSeparation 10 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellGeometry10_eu_oai := @OAI.AtomicTriangular.Construction.cellGeometry10_eu_oai
