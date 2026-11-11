-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialOrbit.weighted_shape_fiber_count
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T05:48:56.361093+00:00
-- url     : https://prove2.me/submissions/3fb63c69-3a54-42b2-bdd4-a66924bc3f3f

import Mathlib
import Definitions.Def_OAIQ254M000

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_InitialOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldInitialOrbit

open AllFieldParameters AllFieldHistory AllFieldInitialEntropy
open scoped BigOperators

theorem weighted_shape_fiber_count_oai : ∀ u ∈ shapes 16,
    (∑ p : PlacedInitial,
      if physicalShape p.2 (sortedInitial.get p.1) = u
      then initialMultiplicity (sortedInitial.get p.1) else 0) = 6 := by
  decide +kernel

end MatrixMultiplication.AllFieldInitialOrbit

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialOrbit.weighted_shape_fiber_count_oai := @OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialOrbit.weighted_shape_fiber_count_oai
