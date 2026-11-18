-- Prove2me | solution 1 for OAI.ElementaryPositivity.TriangularDynamics.historyWeight_positive
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T20:13:55.433902+00:00
-- url     : https://prove2.me/submissions/d0b84740-8088-49eb-9c8e-b643e19dd07a

import Mathlib
import Definitions.Def_ElementaryPositivity
import Definitions.Def_OAIQ368Chrom059

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Witness_ElementarySingletonCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ} (G:NaturalUnitIntervalGraph n)

lemma historyWeight_positive_oai (l:HistoryLeaf G) : LaurentPositive.Positive (historyWeight G l):=
  (historySyntax G).leafWeight_positive _ _ _ _ (historySyntax_positive G) l.val

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

theorem solution : type_of% @OAI.ElementaryPositivity.TriangularDynamics.historyWeight_positive_oai := @OAI.ElementaryPositivity.TriangularDynamics.historyWeight_positive_oai
