-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cellGeometry05_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:13:50.077982+00:00
-- url     : https://prove2.me/submissions/c56ce6a3-6bcb-4444-af2c-450763e6447b

import Mathlib
import Definitions.Def_OAIQ257X011

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGrid0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellGeometry05_x_oai (k : Fin 100) :
    0 ≤ cellMagnitude 5 k ∧ cellMagnitude 5 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 5 → 0 ≤ cellSeparation 5 k j ∧ cellSeparation 5 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 5 k ∧ cellMagnitude 5 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 5 → 0 ≤ cellSeparation 5 k j ∧ cellSeparation 5 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cellGeometry05_x_oai := @OAI.AtomicTriangular.Construction.cellGeometry05_x_oai
