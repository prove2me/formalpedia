-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellGeometry12_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:09:51.848121+00:00
-- url     : https://prove2.me/submissions/b6777b55-9f6c-414d-acbb-111a5eb2b766

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
lemma cellGeometry12_eu_oai (k : Fin 100) :
    0 ≤ cellMagnitude 12 k ∧ cellMagnitude 12 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 12 → 0 ≤ cellSeparation 12 k j ∧ cellSeparation 12 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 12 k ∧ cellMagnitude 12 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 12 → 0 ≤ cellSeparation 12 k j ∧ cellSeparation 12 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellGeometry12_eu_oai := @OAI.AtomicTriangular.Construction.cellGeometry12_eu_oai
